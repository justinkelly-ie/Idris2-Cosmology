module Math.Cosmology.GaloisAdjunction

import Data.Vect
import Core.BoxInt
import Core.UnixelFraction
import Core.Goh
import Geometry.Applicative
import Geometry.MetricalBounds
import Math.Thermodynamics.PreorderedMonoid
import Core.Order.Preorder

%default total

--------------------------------------------------------------------------------
-- 1. GALOIS ADJUNCTION INTERFACE (alpha -| gamma)
--------------------------------------------------------------------------------

||| Galois Adjunction between concrete state domain `C` and abstract domain `A`.
||| Maps fine-grained state representations to coarse-grained macro envelopes metrically.
public export
interface (PreorderedMonoid concrete, PreorderedMonoid abstractDomain) => 
          GaloisAdjunction concrete abstractDomain where
  ||| Abstraction map alpha: C -> A wrapped inside MetricalEnvelope
  alpha : {dim : Nat} -> {color : MetricColor} -> 
          MetricalEnvelope dim color concrete -> MetricalEnvelope dim color abstractDomain

  ||| Concretization map gamma: A -> C wrapped inside MetricalEnvelope
  gamma : {dim : Nat} -> {color : MetricColor} -> 
          MetricalEnvelope dim color abstractDomain -> MetricalEnvelope dim color concrete

  ||| Widening operator nabla for abstract interpretation over infinite/large lattices
  ||| enforcing a PreservesMetric witness to guarantee isometric scale expansion.
  widenNabla : {n : Nat} -> {color : MetricColor} -> 
              {0 space : VexelSpace (S n) color} -> 
              {matrix : Vect (S n) (Vect (S n) UnixelFraction)} -> 
              (0 prf : PreservesMetric space matrix) -> 
              MetricalEnvelope (S n) color abstractDomain -> 
              MetricalEnvelope (S n) color abstractDomain -> 
              MetricalEnvelope (S n) color abstractDomain

--------------------------------------------------------------------------------
-- 2. ABSTRACT INTERPRETATION COARSE-GRAINING FOR BOXINT
--------------------------------------------------------------------------------

||| Concrete domain state wrapping exact particle counts
public export
record ConcreteDomain where
  constructor MkConcrete
  particleCount : Nat

public export
implementation Semigroup ConcreteDomain where
  (MkConcrete c1) <+> (MkConcrete c2) = MkConcrete (c1 + c2)

public export
implementation Monoid ConcreteDomain where
  neutral = MkConcrete 0

public export
implementation PreorderedMonoid ConcreteDomain where
  preorder (MkConcrete c1) (MkConcrete c2) = natLTE c1 c2
  monotonicStep (MkConcrete c1) (MkConcrete c2) (MkConcrete c3) prf =
    natLTEMonotonic c1 c2 c3 prf

||| Abstract domain state wrapping coarse-grained interval bounds
public export
record AbstractDomain where
  constructor MkAbstract
  upperBound : Nat

public export
implementation Semigroup AbstractDomain where
  (MkAbstract a1) <+> (MkAbstract a2) = MkAbstract (a1 + a2)

public export
implementation Monoid AbstractDomain where
  neutral = MkAbstract 0

public export
implementation PreorderedMonoid AbstractDomain where
  preorder (MkAbstract a1) (MkAbstract a2) = natLTE a1 a2
  monotonicStep (MkAbstract a1) (MkAbstract a2) (MkAbstract a3) prf =
    natLTEMonotonic a1 a2 a3 prf

public export
implementation GaloisAdjunction ConcreteDomain AbstractDomain where
  alpha (BoxSpace space (MkConcrete c)) = BoxSpace space (MkAbstract c)
  gamma (BoxSpace space (MkAbstract a)) = BoxSpace space (MkConcrete a)
  widenNabla prf (BoxSpace space (MkAbstract a1)) (BoxSpace _ (MkAbstract a2)) =
    BoxSpace space (MkAbstract (if natLTE a2 a1 then a1 else a2))

--------------------------------------------------------------------------------
-- 3. COMPILE-TIME GALOIS ADJUNCTION SOUNDNESS PROOF
--------------------------------------------------------------------------------

||| Static compiler proof witness verifying Galois Adjunction identity (gamma . alpha = id).
public export
0 verifyGaloisIdentity : {dim : Nat} -> {color : MetricColor} -> 
                         (c : MetricalEnvelope dim color ConcreteDomain) -> 
                         gamma (the (MetricalEnvelope dim color AbstractDomain) (alpha c)) = c
verifyGaloisIdentity (BoxSpace space (MkConcrete c)) = Refl
