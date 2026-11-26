import WOWII255MinimumLower

/-! 十一阶反例及其阶数的最小性。 -/

namespace WOWII255

open SimpleGraph

/-- 编号 0、1、2 分别为 a、b、c，编号 3 至 6 为 xᵢ，编号 7 至 10 为 yᵢ。 -/
private def rowMask : Fin 11 → ℕ := ![122, 5, 1922, 241, 361, 601, 1081, 12, 20, 36, 68]

private def adj11 (u v : Fin 11) : Prop :=
  u ≠ v ∧ (rowMask u).testBit v.val = true ∧ (rowMask v).testBit u.val = true

def graph11 : SimpleGraph (Fin 11) where
  Adj := adj11
  symm := ⟨by intro u v h; exact ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance : DecidableRel graph11.Adj := by
  intro u v
  unfold graph11 adj11
  infer_instance

private theorem routes (u v : Fin 11) :
    u = v ∨ graph11.Adj u v ∨ ∃ z, graph11.Adj u z ∧ graph11.Adj z v := by
  fin_cases u <;> fin_cases v <;> decide

private theorem short_walk11 (u v : Fin 11) : ∃ p : graph11.Walk u v, p.length ≤ 2 := by
  rcases routes u v with rfl | he | ⟨z, huz, hzv⟩
  · exact ⟨.nil, by simp⟩
  · exact ⟨.cons he .nil, by simp⟩
  · exact ⟨.cons huz (.cons hzv .nil), by simp⟩

theorem connected11 : graph11.Connected := by
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro u v
  exact ⟨(short_walk11 u v).choose⟩

private theorem non_neighbor11 (u : Fin 11) : ∃ v, u ≠ v ∧ ¬graph11.Adj u v := by
  fin_cases u <;> decide

theorem eccentricity11 (u : Fin 11) : graph11.eccent u = 2 := by
  apply le_antisymm
  · apply (eccent_le_iff _ _).mpr
    intro v
    obtain ⟨p, hp⟩ := short_walk11 u v
    exact p.edist_le.trans (by exact_mod_cast hp)
  · obtain ⟨v, huv, hn⟩ := non_neighbor11 u
    have h : 1 < graph11.edist u v :=
      lt_of_not_ge fun hv => (edist_le_one_iff_adj_or_eq.mp hv).elim hn huv
    exact (Order.add_one_le_of_lt h).trans edist_le_eccent

theorem center_count11 : centerCount graph11 = 11 := by
  have heq : graph11.center = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro u
    obtain ⟨v, hv⟩ := graph11.exists_eccent_eq_radius
    exact (graph11.mem_center_iff u).mpr
      ((eccentricity11 u).trans ((eccentricity11 v).symm.trans hv))
  simp [centerCount, heq]

private theorem edge_union11 (u v : Fin 11) (h : graph11.Adj u v) :
    (graph11.neighborFinset u ∪ graph11.neighborFinset v).card = 7 := by
  simp only [neighborFinset_eq_filter]
  revert h
  fin_cases u <;> fin_cases v <;> decide

theorem edge_neighborhood_max11 : edgeNeighborhoodMax graph11 = 7 := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    rintro ⟨u, v⟩ he
    exact (edge_union11 u v (Finset.mem_filter.mp he).2).le
  · have he : graph11.Adj 0 1 := by decide
    have hm : (0, 1) ∈ Finset.univ.filter (fun e : Fin 11 × Fin 11 => graph11.Adj e.1 e.2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
    rw [← edge_union11 0 1 he]
    exact Finset.le_sup (f := fun e => (graph11.neighborFinset e.1 ∪ graph11.neighborFinset e.2).card) hm

private def chosen11 : Finset (Fin 11) := {0, 1, 2}

private theorem chosen_dominates11 (u : Fin 11) : ∃ v ∈ chosen11, graph11.Adj u v := by
  fin_cases u <;> decide

theorem total_domination11 : graph11.totalDominationNumber = 3 := by
  apply le_antisymm
  · apply Nat.sInf_le
    exact ⟨chosen11, ⟨chosen_dominates11, by decide⟩⟩
  · apply totalDomination_ge_three_of_max_lt_order graph11 connected11
    rw [edge_neighborhood_max11, Fintype.card_fin]
    decide

theorem refutes_bound11 : ¬ Bound graph11 := by
  norm_num [Bound, center_count11, edge_neighborhood_max11, total_domination11]

/-- 阶数为 n 的连通简单图反例存在。 -/
def CounterexampleOrder (n : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (ha : DecidableRel G.Adj),
    letI := ha
    2 ≤ n ∧ G.Connected ∧ ¬ Bound G

/-- 原猜想的最小反例恰好有 11 个顶点。 -/
theorem smallest_counterexample_order : IsLeast {n | CounterexampleOrder n} 11 := by
  refine ⟨⟨graph11, inferInstance, by decide, connected11, refutes_bound11⟩, ?_⟩
  intro n hn
  obtain ⟨G, ha, h₂, hG, hbad⟩ := hn
  let _ : DecidableRel G.Adj := ha
  let _ : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simp only [Fintype.card_fin]; omega)
  by_contra h
  exact hbad (bound_of_card_le_ten G hG (by simp only [Fintype.card_fin]; omega))

example : CounterexampleOrder 11 := smallest_counterexample_order.1
example : ¬ CounterexampleOrder 10 := by
  intro h
  have : 11 ≤ 10 := smallest_counterexample_order.2 h
  omega

#print axioms refutes_bound11
#print axioms smallest_counterexample_order

end WOWII255
