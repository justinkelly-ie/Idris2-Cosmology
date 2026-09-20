module Math.Cosmology.CapacityBudget

import public Core
import public Math.Cosmology.MetricLawLedger

%default total

--------------------------------------------------------------------------------
-- 1. MONOMORPHIC NAT POWER & MATH HELPERS
--------------------------------------------------------------------------------

||| Monomorphic Nat exponentiation.
%inline public export
powerNat : Nat -> Nat -> Nat
powerNat base 0 = 1
powerNat base (S k) = base * powerNat base k

--------------------------------------------------------------------------------
-- 2. DYNAMIC COSMOLOGICAL CAPACITY BUDGET BY EPOCH
--------------------------------------------------------------------------------

||| Structural Cosmological Capacity Budget tracking partition allocation across
||| visible matter degrees of freedom (VM), dark energy spectral bits (DE),
||| and dark matter metric law residue (DM).
public export
record CapacityBudget where
  constructor MkCapacityBudget
  vmCapacity : Nat   -- Visible Matter (0 pre-baryogenesis, 27 post-baryogenesis)
  deCapacity : Nat   -- Dark Energy background (128 dyadic boxels)
  dmCapacity : Nat   -- Dark Matter metric law residue (0 at Genesis -> 55 at Epoch 37)

public export
Show CapacityBudget where
  show (MkCapacityBudget vm de dm) =
    "CapacityBudget [VM=" ++ show vm ++ ", DE=" ++ show de ++ ", DM=" ++ show dm ++ 
    " | Total=" ++ show (vm + de + dm) ++ "]"

||| Evaluates total capacity bound of a budget.
%inline public export
totalCapacity : CapacityBudget -> Nat
totalCapacity (MkCapacityBudget vm de dm) = vm + de + dm

--------------------------------------------------------------------------------
-- 3. DYNAMIC BARYOGENESIS & LAW ACCUMULATION TRAJECTORY
--------------------------------------------------------------------------------

||| Evaluates visible matter maxel count for epoch ep (0 pre-baryogenesis, 27 post-baryogenesis).
%inline public export
vmMaxelsAtEpoch : Nat -> Nat
vmMaxelsAtEpoch ep =
  if natLTE ep 1 then 0 else powerNat 3 3

||| Evaluates dark matter metric law count for epoch ep (0 at Genesis -> 55 at Epoch 37).
%inline public export
dmLawsAtEpoch : Nat -> Nat
dmLawsAtEpoch 0 = 0
dmLawsAtEpoch 1 = 0
dmLawsAtEpoch ep =
  if natLTE ep 17 then
    minus ep 1
  else
    17 + (minus ep 18 * 2)

||| Dynamically evaluates the exact capacity budget for epoch ep.
%inline public export
epochCapacityBudget : (ep : Nat) -> CapacityBudget
epochCapacityBudget ep =
  let vm = vmMaxelsAtEpoch ep
      de = powerNat 2 7   -- constant 128 dyadic boxel background
      dm = dmLawsAtEpoch ep
  in MkCapacityBudget vm de dm

||| Genesis Pre-Baryogenesis Vacuum Budget (Epoch 1: VM=0, DE=128, DM=0 -> Total=128).
%inline public export
genesisVacuumBudget : CapacityBudget
genesisVacuumBudget = epochCapacityBudget 1

||| Observer Post-Baryogenesis Saturation Budget (Epoch 37: VM=27, DE=128, DM=55 -> Total=210).
%inline public export
observerEpoch37Budget : CapacityBudget
observerEpoch37Budget = epochCapacityBudget 37

--------------------------------------------------------------------------------
-- 4. FORMAL CONSTRUCTIVE PROOF WITNESSES
--------------------------------------------------------------------------------

||| Proof witness verifying Genesis vacuum state before baryogenesis has VM=0, DM=0, DE=128 (Total=128).
public export
0 prfGenesisPreBaryogenesisTotal128 : Math.Cosmology.CapacityBudget.totalCapacity Math.Cosmology.CapacityBudget.genesisVacuumBudget = 128
prfGenesisPreBaryogenesisTotal128 = Refl

||| Proof witness verifying Observer Epoch 37 after baryogenesis reaches Primorial 210 capacity (Total=210).
public export
0 prfObserverEpoch37SaturationTotal210 : Math.Cosmology.CapacityBudget.totalCapacity Math.Cosmology.CapacityBudget.observerEpoch37Budget = 210
prfObserverEpoch37SaturationTotal210 = Refl
