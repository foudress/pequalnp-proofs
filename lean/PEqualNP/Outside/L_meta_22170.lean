import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22170

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [12, 9]⟩,
      ⟨GateOp.and, [13, 11]⟩,
      ⟨GateOp.or, [14, 4]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.and, [16, 2]⟩,
      ⟨GateOp.or, [17, 15]⟩,
      ⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.and, [19, 10]⟩,
      ⟨GateOp.or, [20, 18]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841205 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22170

theorem PEqualNP.Outside.L_meta_22170 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841205 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22170.ckt, PEqualNP.Outside.L_meta_22170.mono, by decide, PEqualNP.Outside.L_meta_22170.rep⟩
