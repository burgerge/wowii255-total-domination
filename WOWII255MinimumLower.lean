import WOWII255Incidence

/-! 排除至多十个顶点的反例。 -/

namespace WOWII255

open SimpleGraph

section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem neighborhood_union_le {u v : V} (h : G.Adj u v) :
    (G.neighborFinset u ∪ G.neighborFinset v).card ≤ edgeNeighborhoodMax G := by
  have he : (u, v) ∈ Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  exact Finset.le_sup (f := fun e => (G.neighborFinset e.1 ∪ G.neighborFinset e.2).card) he

private theorem closed_neighborhood_subset {u v : V} (h : G.Adj u v) :
    insert u (G.neighborFinset u) ⊆ G.neighborFinset u ∪ G.neighborFinset v := by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr h.symm)
  · exact Finset.mem_union_left _ hw

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem walk_stays {A : Finset V} {u v : V} (p : G.Walk u v)
    (h : ∀ ⦃x y⦄, x ∈ A → G.Adj x y → y ∈ A) (hu : u ∈ A) : v ∈ A := by
  induction p with
  | nil => exact hu
  | cons he _ ih => exact ih (h hu he)

private theorem degree_add_two_le [Nontrivial V] (hG : G.Connected)
    (hM : edgeNeighborhoodMax G < Fintype.card V) (u : V) :
    G.degree u + 2 ≤ edgeNeighborhoodMax G := by
  by_contra h
  have hle : edgeNeighborhoodMax G ≤ G.degree u + 1 := by omega
  let A := insert u (G.neighborFinset u)
  have hu : u ∈ A := Finset.mem_insert_self _ _
  have hA : A.card = G.degree u + 1 := by
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self u),
      card_neighborFinset_eq_degree]
  have hclosed : ∀ ⦃x y⦄, x ∈ A → G.Adj x y → y ∈ A := by
    intro x y hx hxy
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr hxy)
    · have hux := (G.mem_neighborFinset _ _).mp hx
      have hcard := (neighborhood_union_le G hux).trans hle
      rw [← hA] at hcard
      have heq := Finset.eq_of_subset_of_card_le (closed_neighborhood_subset G hux) hcard
      change y ∈ insert u (G.neighborFinset u)
      rw [heq]
      exact Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr hxy)
  have hfull : A = Finset.univ := Finset.eq_univ_of_forall fun y =>
    let ⟨p⟩ := hG u y
    walk_stays G p hclosed hu
  obtain ⟨v, hv⟩ := hG.preconnected.exists_adj_of_nontrivial u
  have hm := (Finset.card_le_card (closed_neighborhood_subset G hv)).trans
    (neighborhood_union_le G hv)
  change A.card ≤ edgeNeighborhoodMax G at hm
  rw [hfull, Finset.card_univ] at hm
  exact hM.not_ge hm

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem minimum_set [Nontrivial V] (hG : G.Connected) :
    ∃ D : Finset V, G.IsTotalNDominatingSet G.totalDominationNumber D := by
  have h_exists : {n : ℕ | ∃ D : Finset V, G.IsTotalNDominatingSet n D}.Nonempty := by
    refine ⟨Fintype.card V, Finset.univ, ⟨?_, Finset.card_univ⟩⟩
    intro u
    obtain ⟨v, hv⟩ := hG.preconnected.exists_adj_of_nontrivial u
    exact ⟨v, Finset.mem_univ _, hv⟩
  exact Nat.sInf_mem h_exists

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem totalDomination_ge_two [Nonempty V] {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) : 2 ≤ D.card := by
  obtain ⟨u, hu, _⟩ := hD (Classical.choice ‹Nonempty V›)
  obtain ⟨v, hv, huv⟩ := hD u
  by_contra h
  have hle : D.card ≤ 1 := by omega
  exact huv.ne ((Finset.card_le_one.mp hle) u hu v hv)

private theorem order_le_domination_times_degree_bound {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) {d : ℕ} (hd : ∀ v, G.degree v ≤ d) :
    Fintype.card V ≤ D.card * d := by
  have hcov : D.biUnion (fun v => G.neighborFinset v) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    obtain ⟨v, hv, hxv⟩ := hD x
    exact Finset.mem_biUnion.mpr ⟨v, hv, (G.mem_neighborFinset _ _).mpr hxv.symm⟩
  calc
    Fintype.card V = (D.biUnion fun v => G.neighborFinset v).card := by simp [hcov]
    _ ≤ ∑ v ∈ D, (G.neighborFinset v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ D, d := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [card_neighborFinset_eq_degree] using hd v
    _ = D.card * d := by simp

private theorem order_le_max_of_domination_pair {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : D.card = 2) :
    Fintype.card V ≤ edgeNeighborhoodMax G := by
  obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hcard
  have hab : G.Adj a b := by
    obtain ⟨v, hv, hav⟩ := hD a
    rcases (by simpa using hv : v = a ∨ v = b) with rfl | rfl
    · exact (hav.ne rfl).elim
    · exact hav
  have hcov : G.neighborFinset a ∪ G.neighborFinset b = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    obtain ⟨v, hv, hxv⟩ := hD x
    rcases (by simpa using hv : v = a ∨ v = b) with rfl | rfl
    · exact Finset.mem_union_left _ ((G.mem_neighborFinset _ _).mpr hxv.symm)
    · exact Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr hxv.symm)
  simpa only [hcov, Finset.card_univ] using neighborhood_union_le G hab

/-- 边邻域不能覆盖全图时，两个顶点不足以总支配。 -/
theorem totalDomination_ge_three_of_max_lt_order [Nontrivial V]
    (hG : G.Connected) (hM : edgeNeighborhoodMax G < Fintype.card V) :
    3 ≤ G.totalDominationNumber := by
  obtain ⟨D, hD⟩ := minimum_set G hG
  have h₂ := totalDomination_ge_two G hD.isTotalDominating
  by_contra h
  have hcard : D.card = 2 := by have := hD.card_eq; omega
  exact hM.not_ge (order_le_max_of_domination_pair G hD.isTotalDominating hcard)

private theorem order_add_three_le_of_path_dominates {a b c : V} (hab : G.Adj a b)
    (hbc : G.Adj b c) (hac : a ≠ c)
    (hD : G.IsTotalDominating ({a, b, c} : Finset V)) :
    Fintype.card V + 3 ≤ 2 * edgeNeighborhoodMax G := by
  let X := G.neighborFinset a ∪ G.neighborFinset b
  let Y := G.neighborFinset b ∪ G.neighborFinset c
  have hU : X ∪ Y = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    obtain ⟨v, hv, hxv⟩ := hD x
    rcases (by simpa using hv : v = a ∨ v = b ∨ v = c) with rfl | rfl | rfl <;>
      simp [X, Y, hxv.symm]
  have hs : ({a, b, c} : Finset V) ⊆ X ∩ Y := by
    intro x hx
    rcases (by simpa using hx : x = a ∨ x = b ∨ x = c) with rfl | rfl | rfl <;>
      simp [X, Y, hab, hab.symm, hbc, hbc.symm]
  have hcard : ({a, b, c} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨a, b, c, hab.ne, hac, hbc.ne, rfl⟩
  have hI : 3 ≤ (X ∩ Y).card := hcard ▸ Finset.card_le_card hs
  have hX : X.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hab
  have hY : Y.card ≤ edgeNeighborhoodMax G := neighborhood_union_le G hbc
  have hsum := Finset.card_union_add_card_inter X Y
  rw [hU, Finset.card_univ] at hsum
  omega

omit [Fintype V] [DecidableRel G.Adj] in
private theorem in_domination_triple {a b c : V}
    (hD : G.IsTotalDominating ({a, b, c} : Finset V)) {x : V} (hne : x = a) :
    G.Adj x b ∨ G.Adj x c := by
  obtain ⟨v, hv, hxv⟩ := hD x
  rcases (by simpa using hv : v = a ∨ v = b ∨ v = c) with rfl | rfl | rfl
  · exact (hxv.ne hne).elim
  · exact Or.inl hxv
  · exact Or.inr hxv

private theorem order_add_three_le_of_domination_triple {D : Finset V}
    (hD : G.IsTotalDominating (D : Set V)) (hcard : D.card = 3) :
    Fintype.card V + 3 ≤ 2 * edgeNeighborhoodMax G := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  by_cases h₁ : G.Adj a b
  · have hthird : G.Adj c a ∨ G.Adj c b := by
      apply in_domination_triple G ?_ rfl
      have heq : ({c, a, b} : Finset V) = {a, b, c} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rwa [heq]
    rcases hthird with hca | hcb
    · apply order_add_three_le_of_path_dominates G h₁.symm hca.symm hbc
      simpa only [Finset.insert_comm] using hD
    · exact order_add_three_le_of_path_dominates G h₁ hcb.symm hac hD
  · have ha := (in_domination_triple G hD rfl).resolve_left h₁
    have hswap : G.IsTotalDominating ({b, a, c} : Finset V) := by
      simpa only [Finset.insert_comm] using hD
    have hb := (in_domination_triple G hswap rfl).resolve_left (fun h => h₁ h.symm)
    apply order_add_three_le_of_path_dominates G ha hb.symm hab
    simpa only [Finset.pair_comm] using hD

/-- 十阶及以下满足更强的、以全体顶点数为分子的界。 -/
theorem order_times_two_le_domination_mul_max_of_card_le_ten [Nontrivial V]
    (hG : G.Connected) (hN : Fintype.card V ≤ 10) :
    2 * Fintype.card V ≤ G.totalDominationNumber * edgeNeighborhoodMax G := by
  obtain ⟨D, hD⟩ := minimum_set G hG
  have hg := totalDomination_ge_two G hD.isTotalDominating
  by_contra h
  have hlt : D.card * edgeNeighborhoodMax G < 2 * Fintype.card V := by
    rw [hD.card_eq]
    omega
  have hM : edgeNeighborhoodMax G < Fintype.card V := by
    by_contra hge
    have hm := Nat.mul_le_mul hg (Nat.le_of_not_gt hge)
    omega
  have hdeg (u : V) : G.degree u ≤ edgeNeighborhoodMax G - 2 := by
    have hu := degree_add_two_le G hG hM u
    omega
  have hprod := order_le_domination_times_degree_bound G hD.isTotalDominating hdeg
  have hm₂ : 2 ≤ edgeNeighborhoodMax G := by
    obtain ⟨u⟩ := hG.nonempty
    have hu := degree_add_two_le G hG hM u
    omega
  have hsum : D.card * (edgeNeighborhoodMax G - 2) + 2 * D.card =
      D.card * edgeNeighborhoodMax G := by
    calc
      _ = D.card * (edgeNeighborhoodMax G - 2 + 2) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hm₂]
  have hsmall : 2 * D.card < Fintype.card V := by omega
  have hcases : D.card = 2 ∨ D.card = 3 ∨ D.card = 4 := by omega
  rcases hcases with h₂ | h₃ | h₄
  · have hbig := order_le_max_of_domination_pair G hD.isTotalDominating h₂
    rw [h₂] at hlt
    omega
  · have hbig := order_add_three_le_of_domination_triple G hD.isTotalDominating h₃
    rw [h₃] at hlt
    omega
  · rw [h₄] at hlt hsmall hprod
    omega

theorem bound_of_card_le_ten [Nontrivial V] (hG : G.Connected)
    (hN : Fintype.card V ≤ 10) : Bound G := by
  obtain ⟨v⟩ := hG.nonempty
  obtain ⟨u, hu⟩ := hG.preconnected.exists_adj_of_nontrivial v
  have hM : (0 : ℝ) < edgeNeighborhoodMax G :=
    by exact_mod_cast edgeNeighborhoodMax_pos_of_edge G hu
  unfold Bound
  apply (div_le_iff₀ hM).mpr
  have h := (Nat.mul_le_mul_left 2 (centerCount_le_order G)).trans
    (order_times_two_le_domination_mul_max_of_card_le_ten G hG hN)
  exact_mod_cast h

#print axioms order_times_two_le_domination_mul_max_of_card_le_ten
#print axioms bound_of_card_le_ten

end

end WOWII255
