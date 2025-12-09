### Production of the chains
struct MultiplicationChainFactory{ChainType} <: HyperComplexChainFactory{ChainType}
  # Fields needed for production
	r::RingElem
	M::ModuleFP

  function MultiplicationChainFactory(r::RingElem)
    # Fill in the constructor
    new{ModuleFP}(r, free_module(parent(r),1))
  end
end

function (fac::MultiplicationChainFactory)(self::AbsHyperComplex, i::Tuple)
  # Production of the chains at index i
  return fac.M
end

function can_compute(fac::MultiplicationChainFactory, self::AbsHyperComplex, i::Tuple)
  # Deciding whether the entry at index i can be produced
  return i[1] in 0:1
end

### Production of the morphisms 
struct MultiplicationMapFactory{MorphismType} <: HyperComplexMapFactory{MorphismType}
  # Fields needed for production

  function MultiplicationMapFactory()
    # Fill in the constructor
	new{ModuleFPHom}()
  end
end

function (fac::MultiplicationMapFactory)(self::AbsHyperComplex,p::Int,i::Tuple)
  # Production of the outgoing morphism at index i in the p-th direction
  fac = chain_factory(self)
  return hom(fac.M,fac.M,[fac.r*fac.M[1]])
end

function can_compute(fac::MultiplicationMapFactory, self::AbsHyperComplex, p::Int,i::Tuple)
  # Deciding whether the outgoing map at index i in the p-th direction can be produced
  return (i[1] == 1)
end

### The concrete struct
@attributes mutable struct MultiplicationComplex{ChainType, MorphismType} <: AbsHyperComplex{ChainType, MorphismType} 
  internal_complex::HyperComplex{ChainType, MorphismType}

  function MultiplicationComplex(r::RingElem)
    chain_fac = MultiplicationChainFactory(r)
    map_fac = MultiplicationMapFactory()

    # Assuming d is the dimension of the new complex
    internal_complex = HyperComplex(1, chain_fac, map_fac, [:chain]; lower_bounds = [0], upper_bounds = [1])
    # Assuming that ChainType and MorphismType are provided by the input
    return new{ModuleFP, ModuleFPHom}(internal_complex)
  end
end

### Implementing the AbsHyperComplex interface via `underlying_complex`
underlying_complex(c::MultiplicationComplex) = c.internal_complex

function factor(M::MultiplicationComplex)
	return chain_factory(M).r
end
