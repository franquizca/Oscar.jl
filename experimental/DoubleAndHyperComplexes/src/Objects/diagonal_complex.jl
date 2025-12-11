### Production of the chains
struct DiagonalChainFactory{ChainType} <: HyperComplexChainFactory{ChainType}
  # Fields needed for production
  T::TotalComplex
  W::WedgeComplex
  C::ContractionComplex
  M::MultiplicationComplex
  xi::ModuleFPHom

  function DiagonalChainFactory(W::WedgeComplex,M::MultiplicationComplex,xi::ModuleFPHom,truncation::Int)
    # Fill in the constructor
    C = ContractionComplex(xi; max = truncation)
    T = total_complex(tensor_product(W,M))
    new{ModuleFP}(T,W,C,M,xi)
  end
end

function (fac::DiagonalChainFactory)(self::AbsHyperComplex, i::Tuple)
  # Production of the chains at index i
  i[2] == 0 && return fac.C[i[1]]
  return fac.T[i[1] - i[2] + 1]
end

function can_compute(fac::DiagonalChainFactory, self::AbsHyperComplex, i::Tuple)
  # Deciding whether the entry at index i can be produced
  return (i[1] + 1 >= i[2]) && (i[2] >= 0) && (i[1] in range(fac.C))
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
  h = Oscar.factor(fac.M)
  dh = Oscar.wedge_as_element(fac.W)
  M = fac.C[1]
  R1 = fac.C[0]
  p == 2 && (i == (0,1) && return hom(self[0,1], R1, [h*w for w in gens(R1)]))
  p == 2 && (!(i[2] == 1) && return map(T,i[1] - i[2] + 1))
  dom_inds = Oscar.indices_in_summand(T,i[1] - i[2] + 1)
  projs = map(t -> Oscar.projection(T,t),dom_inds)
  comps = []
  if p == 2
	  codom = fac.C[i[1]]
  	for j in 1:length(dom_inds)
  		dom = codomain(projs[j])
  		dom_iso = get_attribute(dom, :tensor_product)[1]
  		iso = hom(dom,dom_iso,[w for w in gens(dom_iso)])
  		if dom_inds[j][1] == i[1]
  			mult_map = hom(dom_iso,codom,[-h*w for w in gens(codom)])
  		elseif dom_inds[j][1] == 0
  			mult_map = hom(dom_iso,codom,[dh])
  		else
  			mult_map = wedge_multiplication_map(dom_iso,codom,dh)
  		end
  		push!(comps,compose(projs[j],compose(iso,mult_map)))
  	end
  else
	  xi = fac.xi
  	codom_inds = Oscar.indices_in_summand(T,i[1] - i[2])
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
    	  disc = codom_inds[j2][1] - dom_inds[j1][1]
    	  if disc > -2
    	    dom_factors = get_attribute(dom, :tensor_product)
    	    codom_factors = get_attribute(codom, :tensor_product)
    	    if disc == 0
    	    	mult_map = hom(dom_factors[1],codom_factors[1],[special_factor*w for w in gens(codom_factors[1])])
    		  else
    		  	xi = map(fac.C,dom_inds[j1][1])
    		  	codomain_iso = hom(codomain(xi), codom_factors[1],[w for w in gens(codom_factors[1])])
    		  	xi = compose(xi,codomain_iso)
    		  	sgn = (-1)^(dom_inds[j1][1] - (i[1] - i[2])+1)
    		  	mult_map = hom(dom_factors[1],codom_factors[1],[sgn*xi(w) for w in gens(fac.C[dom_inds[j1][1]])])
    		  end
    		  id = hom(dom_factors[2],codom_factors[2],gens(codom_factors[2]))
    		  m = hom_tensor(dom,codom,[mult_map,id])
    	    push!(comps,compose(proj,compose(m,inj)))
    	  else
    	    push!(comps, compose(proj,compose(hom(dom,codom,[zero(codom) for w in gens(dom)]),inj)))
    	  end
    	end
    end
    codom = codomain(injs[1])
  end
  dom = domain(projs[1])
  return hom(dom,codom,[sum(map(f -> f(w),comps)) for w in gens(dom)])
end

function can_compute(fac::DiagonalMapFactory, self::AbsHyperComplex, p::Int, i::Tuple)
  # Deciding whether the outgoing map at index i in the p-th direction can be produced
  fac = chain_factory(self)
  i[2] == 0 && return ((p == 1) && (i[1] in range(fac.C)))
  in_diagonal_line = i[1] - i[2] + 1
  in_diagonal_line == 0 && return p == 2
  in_diagonal_line > 0 && return (i[1] in range(fac.C))
  return false
end

### The concrete struct
@attributes mutable struct DiagonalComplex{ChainType, MorphismType} <: AbsHyperComplex{ChainType, MorphismType} 
  internal_complex::HyperComplex{ChainType, MorphismType}

  function DiagonalComplex(W::WedgeComplex, M::MultiplicationComplex, xi::ModuleFPHom; max::Union{Nothing,Int} = nothing)
  	max == nothing && (max = ngens(domain(xi)))
    chain_fac = DiagonalChainFactory(W,M,xi,max)
    map_fac = DiagonalMapFactory()

    # Assuming d is the dimension of the new complex
    internal_complex = HyperComplex(2, chain_fac, map_fac, [:chain for i in 1:2]; lower_bounds = [0,0], upper_bounds = [max, max+1])
    # Assuming that ChainType and MorphismType are provided by the input
    return new{ModuleFP, ModuleFPHom}(internal_complex)
  end
end

### Implementing the AbsHyperComplex interface via `underlying_complex`
underlying_complex(c::DiagonalComplex) = c.internal_complex

function original_complex(D::DiagonalComplex)
	return chain_factory(D).T
end
	
