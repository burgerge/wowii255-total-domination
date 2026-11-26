import WOWII256

/-! 第 256 题的十四阶见证。 -/

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax totalDomination_ge_three_of_max_lt_order)

/-- 0、1、2 是总支配路径。3 至 13 是一个十一点环，0 连 4 至 8，
1 连 3，2 连 9 至 13。 -/
private def rowMask : Fin 14 → ℕ := ![498, 13, 15874, 8210, 41, 81, 161, 321, 641, 1284, 2564, 5124, 10244, 4108]

private def adj14 (u v : Fin 14) : Prop :=
  u ≠ v ∧ (rowMask u).testBit v.val = true ∧ (rowMask v).testBit u.val = true

def graph14 : SimpleGraph (Fin 14) where
  Adj := adj14
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance : DecidableRel graph14.Adj := by
  intro u v
  unfold graph14 adj14
  infer_instance

private theorem hubRoute (v : Fin 14) :
    v = 1 ∨ graph14.Adj v 1 ∨ ∃ u, graph14.Adj v u ∧ graph14.Adj u 1 := by
  fin_cases v <;> decide

theorem connected14 : graph14.Connected := by
  have reach (v : Fin 14) : graph14.Reachable v 1 := by
    rcases hubRoute v with h | h | ⟨u, hv, hz⟩
    · subst v
      exact ⟨.nil⟩
    · exact ⟨h.toWalk⟩
    · exact ⟨.cons hv hz.toWalk⟩
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro u v
  exact (reach u).trans (reach v).symm

private def degreeValue14 (u : Fin 14) : ℕ :=
  if u = 0 ∨ u = 2 then 6 else 3

private theorem degree14 (u : Fin 14) : graph14.degree u = degreeValue14 u := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  fin_cases u <;> decide

theorem min_degree_neighborhood_count14 : (minDegreeNeighborhood graph14).card = 14 := by
  have h : minDegreeNeighborhood graph14 = Finset.univ := by
    ext v
    simp only [minDegreeNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have hAdj (x : Fin 14) : ∃ u, graph14.Adj x u ∧ degreeValue14 u = 3 := by
      fin_cases x <;> decide
    obtain ⟨u, hvu, hu⟩ := hAdj v
    refine ⟨u, hvu, fun w => ?_⟩
    rw [degree14, degree14, hu]
    unfold degreeValue14
    split_ifs <;> decide
  rw [h, Finset.card_univ, Fintype.card_fin]

private theorem edgeUnionLe (u v : Fin 14) (h : graph14.Adj u v) :
    (graph14.neighborFinset u ∪ graph14.neighborFinset v).card ≤ 9 := by
  simp only [neighborFinset_eq_filter]
  revert h
  fin_cases u <;> fin_cases v <;> decide

theorem edge_neighborhood_max14 : edgeNeighborhoodMax graph14 = 9 := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    rintro ⟨u, v⟩ he
    exact edgeUnionLe u v (Finset.mem_filter.mp he).2
  · have he : (0, 1) ∈ Finset.univ.filter (fun e : Fin 14 × Fin 14 => graph14.Adj e.1 e.2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩
    have hcard : (graph14.neighborFinset 0 ∪ graph14.neighborFinset 1).card = 9 := by
      simp only [neighborFinset_eq_filter]
      decide
    rw [← hcard]
    exact Finset.le_sup
      (f := fun e => (graph14.neighborFinset e.1 ∪ graph14.neighborFinset e.2).card) he

private def chosen14 : Finset (Fin 14) := {0, 1, 2}

theorem total_domination14 : graph14.totalDominationNumber = 3 := by
  apply le_antisymm
  · apply Nat.sInf_le
    have hd (v : Fin 14) : ∃ u ∈ chosen14, graph14.Adj v u := by
      fin_cases v <;> decide
    exact ⟨chosen14, ⟨hd, by decide⟩⟩
  · exact totalDomination_ge_three_of_max_lt_order graph14 connected14
      (by simp [edge_neighborhood_max14])

theorem refutes_bound14 : ¬ Bound graph14 := by
  norm_num [Bound, min_degree_neighborhood_count14, total_domination14, edge_neighborhood_max14]

#print axioms refutes_bound14

end WOWII256
