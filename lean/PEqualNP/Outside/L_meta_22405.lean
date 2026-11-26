import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22405

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [9, 4]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [3, 0]⟩,
      ⟨GateOp.or, [13, 8]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.and, [12, 14]⟩,
      ⟨GateOp.and, [16, 11]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.and, [15, 2]⟩,
      ⟨GateOp.or, [20, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (904047 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22405

theorem PEqualNP.Outside.L_meta_22405 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904047 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22405.ckt, PEqualNP.Outside.L_meta_22405.mono, by decide, PEqualNP.Outside.L_meta_22405.rep⟩
