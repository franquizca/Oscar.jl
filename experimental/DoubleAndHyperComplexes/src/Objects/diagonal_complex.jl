### Production of the chains
struct DiagonalChainFactory{ChainType} <: HyperComplexChainFactory{ChainType}
  # Fields needed for production
    T::TotalComplex
    C::ContractionComplex
    M::MultiplicationComplex

  function DiagonalChainFactory(C::ContractionComplex,M::MultiplicationComplex)
    # Fill in the constructor
    T = total_complex(tensor_product(C,M))
        new{ModuleFP}(T,C,M)
  end
end

function (fac::DiagonalChainFactory)(self::AbsHyperComplex, i::Tuple)
  # Production of the chains at index i
    i[2] == 0 && return fac.C[i[1]]
    return fac.T[i[1] - i[2] + 1]
end

function can_compute(fac::DiagonalChainFactory, self::AbsHyperComplex, i::Tuple)
  # Deciding whether the entry at index i can be produced
  i[2] == 0 && return i[1] in range(fac.C)
  return ((i[1] - i[2] + 1) in range(fac.T)) && (i[2] > 0)
end

### Production of the morphisms 
struct DiagonalMapFactory{MorphismType} <: HyperComplexMapFactory{MorphismType}
  # Fields needed for production

  function DiagonalMapFactory()
    # Fill in the constructor
        new{ModuleFPHom}()
  end
end

function (fac::DiagonalMapFactory)(self::AbsHyperComplex, p::Int, i::Tuple)
  # Production of the outgoing morphism at index i in the p-th direction
    fac = chain_factory(self)
    T = fac.T
    i[2] == 0 && return map(fac.C,i[1])
    p == 1 && return map(T,i[1] - i[2] + 1)
    h = Oscar.factor(fac.M)
    M = fac.C[1]
    R1 = fac.C[0]
    (i[2] == 1 && i[1] == 0) && return compose(hom(T[0],R1, gens(R1)),hom(R1,R1,[h*R1[1]]))
    dh = exterior_derivative(h; parent = M)
    dom_inds = Oscar.indices_in_summand(T,i[1] - i[2] + 1)
    projs = map(t -> Oscar.projection(T,t),dom_inds)
    comps = []
    if i[2] == 1
    	codom = fac.C[i[1]]
    	for j in 1:length(dom_inds)
    		dom = codomain(projs[j])
    		C = get_attribute(dom, :tensor_product)[1]
   		 	id = hom(dom,C, gens(C))
  		  	if i[1] - dom_inds[j][1] == 0
        	    mult_map = hom(C, codom,map(e -> h*e,gens(codom)))
       		else
        	    if dom_inds[j][1] == 0
        	    	mult_map = hom(C,codom,[dh])
        	    else
	        	    mult_map = Oscar.wedge_multiplication_map(C,codom,dh)
       			end
       		end
        	push!(comps,compose(projs[j],compose(id,mult_map)))
        end
        dom = domain(projs[1])
    else
	    codom_inds = Oscar.indices_in_summand(T,i[1] - i[2] + 2)
   		injs = map(t -> Oscar.injection(T,t),codom_inds)
   		xi = map(fac.C,1)
   		num = xi(dh)[1]
   		special_factor = num / h
    	for j1 in 1:length(dom_inds)
    	    for j2 in 1:length(codom_inds)
    	        proj = projs[j1]
    	        dom = codomain(proj)
    	        inj = injs[j2]
    	        codom = domain(inj)
    	        disc = codom_inds[j2][2] - dom_inds[j1][2]
    	        if disc >= 0
    	        	comp = Oscar.tensor_pure_function(codom)
    	            dom_factors = get_attribute(dom, :tensor_product)
    	            codom_factors = get_attribute(codom, :tensor_product)
    	            if disc == 0
	    	            dom_power = dom_inds[j1][1]
   		 	            if dom_power == 0
    		    	    	wdg = hom(dom_factors[1], codom_factors[1], [dh])
    		    	    else
    		    	    	wdg = Oscar.wedge_multiplication_map(dom_factors[1],codom_factors[1],dh)
    		    	    end
    		    	    id = hom(dom_factors[2],codom_factors[2],gens(codom_factors[2]))
    		            m = hom_tensor(dom,codom,[wdg,id])
    		        else
    		        	id = hom(dom_factors[1],codom_factors[1],gens(codom_factors[1]))
    		        	mult_map = hom(dom_factors[2],codom_factors[2],map(e -> special_factor*e, gens(codom_factors[2])))
    		        	m = hom_tensor(dom,codom,[id,mult_map])
    		        end
    	            push!(comps,compose(proj,compose(m,inj)))
    	        else
    	            push!(comps, compose(proj,compose(hom(dom,codom,[zero(codom) for w in gens(dom)]),inj)))
    	        end
    	    end
    	end
    	dom = domain(projs[1])
    	codom = codomain(injs[1])
    end
    return hom(dom,codom,[sum(map(f -> f(w),comps)) for w in gens(dom)])
end

function can_compute(fac::DiagonalMapFactory, self::AbsHyperComplex, p::Int, i::Tuple)
  # Deciding whether the outgoing map at index i in the p-th direction can be produced
    fac = chain_factory(self)
    i[2] == 0 && return (p == 1) && (i[1] in range(fac.C))
    p == 1 && return (i[1] - i[2] + 1 > 0) && ((i[1] - i[2] + 1) in range(fac.T)) && (i[2] > 0)
    return (i[2] > 0) && ((i[1] - i[2]+ 1) in range(fac.T)) && (i[1] - i[2] + 1 < range(fac.T)[1])
end

### The concrete struct
@attributes mutable struct DiagonalComplex{ChainType, MorphismType} <: AbsHyperComplex{ChainType, MorphismType} 
  internal_complex::HyperComplex{ChainType, MorphismType}

  function DiagonalComplex(C::ContractionComplex, M::MultiplicationComplex)
    chain_fac = DiagonalChainFactory(C,M)
    map_fac = DiagonalMapFactory()

    # Assuming d is the dimension of the new complex
    internal_complex = HyperComplex(2, chain_fac, map_fac, [:chain for i in 1:2]; lower_bounds = [0,0])
    # Assuming that ChainType and MorphismType are provided by the input
    return new{ModuleFP, ModuleFPHom}(internal_complex)
  end
end

### Implementing the AbsHyperComplex interface via `underlying_complex`
underlying_complex(c::DiagonalComplex) = c.internal_complex

function original_complex(D::DiagonalComplex)
	return chain_factory(D).T
end
	
