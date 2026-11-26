import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19183

def witness : Circuit :=
  ⟨[⟨.and, [1, 6]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [10, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [11, 14]⟩], 15⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_19183

open PEqualNP.Outside.L_meta_19183 in
theorem PEqualNP.Outside.L_meta_19183 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5806 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
