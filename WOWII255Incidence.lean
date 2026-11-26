import WOWII255

/-! 二分关联图的距离判据，以及总支配数的通用覆盖下界。 -/

namespace WOWII255

open SimpleGraph

section Incidence

variable {P B : Type*} (R : P → B → Prop)

private def incidenceAdj : P ⊕ B → P ⊕ B → Prop
  | .inl p, .inr b => R p b
  | .inr b, .inl p => R p b
  | _, _ => False

/-- 关联关系决定的二分简单图。 -/
def incidenceGraph : SimpleGraph (P ⊕ B) where
  Adj := incidenceAdj R
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact id⟩

instance [DecidableRel R] : DecidableRel (incidenceGraph R).Adj := by
  intro u v
  cases u <;> cases v <;> unfold incidenceGraph incidenceAdj <;> infer_instance

@[simp] theorem incidence_inl_inl (p q : P) :
    ¬ (incidenceGraph R).Adj (.inl p) (.inl q) := id

@[simp] theorem incidence_inr_inr (a b : B) :
    ¬ (incidenceGraph R).Adj (.inr a) (.inr b) := id

@[simp] theorem incidence_inl_inr (p : P) (b : B) :
    (incidenceGraph R).Adj (.inl p) (.inr b) ↔ R p b := Iff.rfl

@[simp] theorem incidence_inr_inl (b : B) (p : P) :
    (incidenceGraph R).Adj (.inr b) (.inl p) ↔ R p b := Iff.rfl

private theorem walk_two {G : SimpleGraph (P ⊕ B)} {u v w : P ⊕ B}
    (h₁ : G.Adj u v) (h₂ : G.Adj v w) : ∃ p : G.Walk u w, p.length ≤ 3 :=
  ⟨.cons h₁ (.cons h₂ .nil), by simp⟩

private theorem walk_three {G : SimpleGraph (P ⊕ B)} {u v w z : P ⊕ B}
    (h₁ : G.Adj u v) (h₂ : G.Adj v w) (h₃ : G.Adj w z) :
    ∃ p : G.Walk u z, p.length ≤ 3 :=
  ⟨.cons h₁ (.cons h₂ (.cons h₃ .nil)), by simp⟩

private theorem incidence_short_walk
    (hP : ∀ p q : P, ∃ b, R p b ∧ R q b)
    (hB : ∀ a b : B, ∃ p, R p a ∧ R p b) (u v : P ⊕ B) :
    ∃ w : (incidenceGraph R).Walk u v, w.length ≤ 3 := by
  rcases u with p | a <;> rcases v with q | b
  · obtain ⟨b, hp, hq⟩ := hP p q
    exact walk_two (v := .inr b) hp hq
  · obtain ⟨q, hq, _⟩ := hB b b
    obtain ⟨a, hp, hqa⟩ := hP p q
    exact walk_three (v := .inr a) (w := .inl q) hp hqa hq
  · obtain ⟨p, hp, _⟩ := hB a a
    obtain ⟨b, hpb, hqb⟩ := hP p q
    exact walk_three (v := .inl p) (w := .inr b) hp hpb hqb
  · obtain ⟨p, ha, hb⟩ := hB a b
    exact walk_two (v := .inl p) ha hb

theorem incidence_connected [Nonempty P]
    (hP : ∀ p q : P, ∃ b, R p b ∧ R q b)
    (hB : ∀ a b : B, ∃ p, R p a ∧ R p b) : (incidenceGraph R).Connected := by
  refine { preconnected := ?_, nonempty := inferInstance }
  intro u v
  exact ⟨(incidence_short_walk R hP hB u v).choose⟩

private theorem opposite_nonadjacent_far (p : P) (b : B) (h : ¬ R p b) :
    3 ≤ (incidenceGraph R).edist (.inl p) (.inr b) := by
  have he : 2 < (incidenceGraph R).edist (.inl p) (.inr b) := by
    apply two_lt_edist_iff.mpr
    refine ⟨by simp, h, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro w hw
    have hw' := ((incidenceGraph R).mem_commonNeighbors).mp hw
    cases w with
    | inl q => exact hw'.1
    | inr a => exact hw'.2
  exact Order.add_one_le_of_lt he

/-- 同侧任意两点有共邻且每个顶点遗漏异侧一点时，全图偏心距均为 3。 -/
theorem incidence_eccentricity
    (hP : ∀ p q : P, ∃ b, R p b ∧ R q b)
    (hB : ∀ a b : B, ∃ p, R p a ∧ R p b)
    (hPm : ∀ p : P, ∃ b, ¬ R p b)
    (hBm : ∀ b : B, ∃ p, ¬ R p b) (u : P ⊕ B) : (incidenceGraph R).eccent u = 3 := by
  apply le_antisymm
  · apply (eccent_le_iff _ _).mpr
    intro v
    obtain ⟨w, hw⟩ := incidence_short_walk R hP hB u v
    exact w.edist_le.trans (by exact_mod_cast hw)
  · cases u with
    | inl p =>
      obtain ⟨b, hb⟩ := hPm p
      exact (opposite_nonadjacent_far R p b hb).trans edist_le_eccent
    | inr b =>
      obtain ⟨p, hp⟩ := hBm b
      have h := opposite_nonadjacent_far R p b hp
      rw [edist_comm] at h
      exact h.trans edist_le_eccent

end Incidence

section LowerBound

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_le_edgeNeighborhoodMax {u v : V} (h : G.Adj u v) :
    G.degree u ≤ edgeNeighborhoodMax G := by
  have he : (u, v) ∈ Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  calc
    G.degree u = (G.neighborFinset u).card := (card_neighborFinset_eq_degree G u).symm
    _ ≤ (G.neighborFinset u ∪ G.neighborFinset v).card :=
      Finset.card_le_card Finset.subset_union_left
    _ ≤ edgeNeighborhoodMax G := Finset.le_sup
      (f := fun e => (G.neighborFinset e.1 ∪ G.neighborFinset e.2).card) he

theorem edgeNeighborhoodMax_pos_of_edge {u v : V} (h : G.Adj u v) :
    0 < edgeNeighborhoodMax G := by
  have hv : v ∈ G.neighborFinset u := by rwa [mem_neighborFinset]
  have hp : 0 < G.degree u := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨v, hv⟩
  exact hp.trans_le (degree_le_edgeNeighborhoodMax G h)

theorem order_le_totalDomination_mul_max (h : ∀ u, ∃ v, G.Adj u v) :
    Fintype.card V ≤ G.totalDominationNumber * edgeNeighborhoodMax G := by
  have h_exists : {n : ℕ | ∃ D : Finset V, G.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card V, Finset.univ, ⟨?_, Finset.card_univ⟩⟩
    intro u
    obtain ⟨v, hv⟩ := h u
    exact ⟨v, Finset.mem_univ _, hv⟩
  have h_min := Nat.sInf_mem h_exists
  change ∃ D : Finset V, G.IsTotalNDominatingSet G.totalDominationNumber D at h_min
  obtain ⟨D, hD⟩ := h_min
  have h_cover : D.biUnion (fun v => G.neighborFinset v) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro u
    obtain ⟨v, hv, huv⟩ := hD.isTotalDominating u
    exact Finset.mem_biUnion.mpr ⟨v, hv, by simpa only [mem_neighborFinset] using huv.symm⟩
  calc
    Fintype.card V = (D.biUnion fun v => G.neighborFinset v).card := by
      rw [h_cover, Finset.card_univ]
    _ ≤ ∑ v ∈ D, (G.neighborFinset v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ D, edgeNeighborhoodMax G := by
      apply Finset.sum_le_sum
      intro u _
      obtain ⟨v, hv⟩ := h u
      rw [card_neighborFinset_eq_degree]
      exact degree_le_edgeNeighborhoodMax G hv
    _ = G.totalDominationNumber * edgeNeighborhoodMax G := by simp [hD.card_eq]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem centerCount_le_order : centerCount G ≤ Fintype.card V := by
  classical
  unfold centerCount
  exact Finset.card_le_univ _

end LowerBound

end WOWII255
