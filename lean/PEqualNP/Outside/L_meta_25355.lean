import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25355_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wit : Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit)
def okOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false
theorem okOpSound (g : Gate) (h : okOp g = true) : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases hg : g.op <;> simp [okOp, hg] at h ⊢
theorem fit : PEqualNP.MetaComplexity.FanInTwo wit := by
  have hl : wit.gates.all (fun g => okOp g && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
  intro g hg
  have hp := List.all_eq_true.mp hl g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using okOpSound g hp.1, hp.2⟩
end PEqualNP.Outside.L_meta_25355_aux

theorem PEqualNP.Outside.L_meta_25355 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197295 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25355_aux.wit, PEqualNP.Outside.L_meta_25355_aux.fit, by decide, ?_⟩
  intro i j
  revert i j
  decide +kernel

