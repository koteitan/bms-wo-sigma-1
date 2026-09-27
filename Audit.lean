/-
Axiom audit of bms-wo-sigma-1.

This file is not part of any `lean_lib`. Check it with
`leanman check -C . Audit.lean` (or `lake env lean Audit.lean`) after building
`Bm4 Por`. Every line below should print
`[propext, Classical.choice, Quot.sound]`.
-/
import Por

-- The final BMS theorems.
#print axioms Por.terminates
#print axioms Por.step_wf
#print axioms Por.R_wf
#print axioms Por.R'_wf

-- The model: the label system, finite reflection, the chain.
#print axioms Por.labelSystem
#print axioms Por.reflect
#print axioms Por.R_trans
#print axioms Por.stable_all
#print axioms Por.chain_R

-- The relation R and its defining equation.
#print axioms Por.R_iff

-- The height descent of the BMS layer that the model is plugged into.
#print axioms BM4.descent
