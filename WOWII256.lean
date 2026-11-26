import WOWII255MinimumLower

/-! Written on the Wall II 第 256 题的二分图反例。 -/

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax totalDomination_ge_three_of_max_lt_order)

section

variable {V : Type*} [Fintype V]

/-- 最小度顶点集合的开邻域。 -/
def minDegreeNeighborhood (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => ∃ u, G.Adj v u ∧ ∀ w, G.degree u ≤ G.degree w)

/-- 在原题第 256 题中，分子为最小度顶点集合的开邻域的基数。 -/
def Bound (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] : Prop :=
  2 * ((minDegreeNeighborhood G).card : ℝ) / (edgeNeighborhoodMax G : ℝ) ≤ G.totalDominationNumber

end

/-- 二分图的左部为 0–17，其中 0–7 是两组各四个原顶点。
右部 18–57 是两组各五批、每批四个普通顶点，58 是公共顶点。 -/
private def cross (u v : Fin 59) : Prop :=
  u.val < 18 ∧ 18 ≤ v.val ∧
    (v.val = 58 ∨
      (u.val < 8 ∧ u.val / 4 = (v.val - 18) / 20) ∨
      (8 ≤ u.val ∧ u.val - 8 = (v.val - 18) / 4))

private instance (u v : Fin 59) : Decidable (cross u v) := by
  unfold cross
  infer_instance

def graph59 : SimpleGraph (Fin 59) where
  Adj u v := cross u v ∨ cross v u
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by
    intro u h
    change cross u u ∨ cross u u at h
    rcases h with h | h <;> exact (Nat.not_lt_of_ge h.2.1) h.1⟩

instance : DecidableRel graph59.Adj := by
  intro u v
  change Decidable (cross u v ∨ cross v u)
  infer_instance

private theorem hub_route (v : Fin 59) :
    v = 58 ∨ graph59.Adj v 58 ∨ ∃ u, graph59.Adj v u ∧ graph59.Adj u 58 := by
  fin_cases v <;> decide

theorem connected59 : graph59.Connected := by
  have reach (v : Fin 59) : graph59.Reachable v 58 := by
    rcases hub_route v with h | h | ⟨u, hv, hz⟩
    · subst v
      exact ⟨.nil⟩
    · exact ⟨h.toWalk⟩
    · exact ⟨.cons hv hz.toWalk⟩
  refine { preconnected := ?_, nonempty := ⟨0⟩ }
  intro u v
  exact (reach u).trans (reach v).symm

private def degreeValue (u : Fin 59) : ℕ :=
  if u.val < 8 then 21 else if u.val = 58 then 18 else 5

private theorem degree59 (u : Fin 59) : graph59.degree u = degreeValue u := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  fin_cases u <;> decide

theorem every_vertex_has_min_degree_neighbor59 :
    ∀ v, ∃ u, graph59.Adj v u ∧ ∀ w, graph59.degree u ≤ graph59.degree w := by
  intro v
  have h (x : Fin 59) : ∃ u, graph59.Adj x u ∧ degreeValue u = 5 := by
    fin_cases x <;> decide
  obtain ⟨u, hvu, hu⟩ := h v
  refine ⟨u, hvu, fun w => ?_⟩
  rw [degree59, degree59, hu]
  unfold degreeValue
  split_ifs <;> decide

theorem min_degree_neighborhood_count59 : (minDegreeNeighborhood graph59).card = 59 := by
  have h : minDegreeNeighborhood graph59 = Finset.univ := by
    ext v
    simp only [minDegreeNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact every_vertex_has_min_degree_neighbor59 v
  rw [h, Finset.card_univ, Fintype.card_fin]

private theorem sum_degree_bound {u v : Fin 59} (h : cross u v) :
    graph59.degree u + graph59.degree v ≤ 39 := by
  rw [degree59, degree59]
  have hu := h.1
  have hv := h.2.1
  unfold degreeValue
  split_ifs <;> omega

private theorem edge_neighborhood_max_le39 : edgeNeighborhoodMax graph59 ≤ 39 := by
  apply Finset.sup_le_iff.mpr
  rintro ⟨u, v⟩ he
  have hadj : cross u v ∨ cross v u := (Finset.mem_filter.mp he).2
  apply (Finset.card_union_le _ _).trans
  simp only [card_neighborFinset_eq_degree]
  rcases hadj with huv | hvu
  · exact sum_degree_bound huv
  · rw [add_comm]
    exact sum_degree_bound hvu

theorem edge_neighborhood_max59 : edgeNeighborhoodMax graph59 = 39 := by
  apply le_antisymm edge_neighborhood_max_le39
  have he : (0, 58) ∈ Finset.univ.filter (fun e : Fin 59 × Fin 59 => graph59.Adj e.1 e.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩
  have hcard : (graph59.neighborFinset 0 ∪ graph59.neighborFinset 58).card = 39 := by
    simp only [neighborFinset_eq_filter]
    decide
  rw [← hcard]
  exact Finset.le_sup (f := fun e => (graph59.neighborFinset e.1 ∪ graph59.neighborFinset e.2).card) he

private def chosen59 : Finset (Fin 59) := {0, 4, 58}

theorem total_domination59 : graph59.totalDominationNumber = 3 := by
  apply le_antisymm
  · apply Nat.sInf_le
    have hd (v : Fin 59) : ∃ u ∈ chosen59, graph59.Adj v u := by
      fin_cases v <;> decide
    exact ⟨chosen59, ⟨hd, by decide⟩⟩
  · exact totalDomination_ge_three_of_max_lt_order graph59 connected59
      (by simp [edge_neighborhood_max59])

theorem refutes_bound59 : ¬ Bound graph59 := by
  norm_num [Bound, min_degree_neighborhood_count59, total_domination59, edge_neighborhood_max59]

/-- 第 256 题在原目录的边邻域与开邻域定义下为假。 -/
theorem conjecture256_false :
    ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → Bound G) := by
  intro h
  exact refutes_bound59 (h graph59 connected59)

#print axioms conjecture256_false

end WOWII256
