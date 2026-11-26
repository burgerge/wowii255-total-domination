import WOWII255Incidence

/-! 用标签的有序对构造中心为全体顶点的二分图。 -/

namespace WOWII255.PairFamily

open SimpleGraph

abbrev Label (k : ℕ) := Bool × Fin (k + 2)
abbrev Point (k : ℕ) := Label k × Label k
abbrev Block (k copies : ℕ) := Bool ⊕ (Label k × Fin copies)
abbrev Vertex (k copies : ℕ) := Point k ⊕ Block k copies

private def fixed (k : ℕ) (b : Bool) : Label k := (b, 0)

private def omitted (k : ℕ) (b : Bool) : Point k := (fixed k b, fixed k false)

private theorem omitted_ne (k : ℕ) : omitted k false ≠ omitted k true := by
  intro h
  have hbit := congrArg (fun p : Point k => p.1.1) h
  simp [omitted, fixed] at hbit

private theorem avoids_omission {k : ℕ} {p : Point k} (h : p.2.1 = true) (b : Bool) :
    p ≠ omitted k b := by
  intro heq
  have hb := congrArg (fun q : Point k => q.2.1) heq
  simp [omitted, fixed, h] at hb

def relation {k copies : ℕ} (p : Point k) : Block k copies → Prop
  | .inl b => p ≠ omitted k b
  | .inr (i, _) => p.1 = i ∨ p.2 = i

instance (k copies : ℕ) : DecidableRel (@relation k copies) := by
  intro p b
  cases b <;> unfold relation <;> infer_instance

def graph (k copies : ℕ) : SimpleGraph (Vertex k copies) :=
  incidenceGraph (@relation k copies)

instance (k copies : ℕ) : DecidableRel (graph k copies).Adj := by
  unfold graph
  infer_instance

private theorem covered_by_large {k : ℕ} (p : Point k) :
    p ≠ omitted k false ∨ p ≠ omitted k true := by
  by_cases h : p = omitted k false
  · exact Or.inr (h ▸ omitted_ne k)
  · exact Or.inl h

private theorem points_share_block {k copies : ℕ} [NeZero copies] (p q : Point k) :
    ∃ b : Block k copies, relation p b ∧ relation q b := by
  by_cases h₀ : p ≠ omitted k false ∧ q ≠ omitted k false
  · exact ⟨.inl false, h₀⟩
  by_cases h₁ : p ≠ omitted k true ∧ q ≠ omitted k true
  · exact ⟨.inl true, h₁⟩
  have h₀' := not_and_or.mp h₀
  have h₁' := not_and_or.mp h₁
  simp only [not_not] at h₀' h₁'
  refine ⟨.inr (fixed k false, 0), ?_⟩
  rcases h₀' with hp | hq <;> rcases h₁' with hp' | hq'
  · exact (omitted_ne k (hp.symm.trans hp')).elim
  · exact ⟨Or.inr (congrArg Prod.snd hp), Or.inr (congrArg Prod.snd hq')⟩
  · exact ⟨Or.inr (congrArg Prod.snd hp'), Or.inr (congrArg Prod.snd hq)⟩
  · exact (omitted_ne k (hq.symm.trans hq')).elim

private theorem blocks_share_point {k copies : ℕ} (a b : Block k copies) :
    ∃ p : Point k, relation p a ∧ relation p b := by
  rcases a with a | ⟨i, r⟩ <;> rcases b with b | ⟨j, s⟩
  · exact ⟨(fixed k true, fixed k true), avoids_omission rfl a, avoids_omission rfl b⟩
  · exact ⟨(j, fixed k true), avoids_omission rfl a, Or.inl rfl⟩
  · exact ⟨(i, fixed k true), Or.inl rfl, avoids_omission rfl b⟩
  · exact ⟨(i, j), Or.inl rfl, Or.inr rfl⟩

private theorem label_card (k : ℕ) : Fintype.card (Label k) = 2 * (k + 2) := by
  simp [Label, Fintype.card_prod, Fintype.card_bool]

private theorem point_card (k : ℕ) :
    Fintype.card (Point k) = (2 * (k + 2)) * (2 * (k + 2)) := by
  rw [Fintype.card_prod, label_card]

private theorem pair_card_le {α : Type*} [DecidableEq α] (u v : α) :
    ({u, v} : Finset α).card ≤ 2 := by
  calc
    _ ≤ ({v} : Finset α).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

private theorem point_misses_block {k copies : ℕ} [NeZero copies] (p : Point k) :
    ∃ b : Block k copies, ¬ relation p b := by
  have hcard : ({p.1, p.2} : Finset (Label k)).card <
      (Finset.univ : Finset (Label k)).card := by
    rw [Finset.card_univ, label_card]
    exact (pair_card_le _ _).trans_lt (by omega)
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨.inr (i, 0), by simpa [relation, eq_comm] using hi⟩

private theorem block_misses_point {k copies : ℕ} (b : Block k copies) :
    ∃ p : Point k, ¬ relation p b := by
  rcases b with b | ⟨i, r⟩
  · exact ⟨omitted k b, fun h => h rfl⟩
  · let j : Label k := (!i.1, i.2)
    have hj : j ≠ i := by
      intro h
      have he := congrArg Prod.fst h
      cases hi : i.1 <;> simp [j, hi] at he
    exact ⟨(j, j), fun h => h.elim hj hj⟩

theorem connected (k copies : ℕ) [NeZero copies] : (graph k copies).Connected :=
  incidence_connected _ points_share_block blocks_share_point

theorem eccentricity (k copies : ℕ) [NeZero copies] (v : Vertex k copies) :
    (graph k copies).eccent v = 3 :=
  incidence_eccentricity _ points_share_block blocks_share_point
    point_misses_block block_misses_point v

theorem all_centers (k copies : ℕ) [NeZero copies] :
    (graph k copies).center = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro u
  obtain ⟨v, hv⟩ := (graph k copies).exists_eccent_eq_radius
  exact ((graph k copies).mem_center_iff u).mpr
    ((eccentricity k copies u).trans ((eccentricity k copies v).symm.trans hv))

theorem center_count (k copies : ℕ) [NeZero copies] : centerCount (graph k copies) =
    (2 * (k + 2)) * (2 * (k + 2)) + (2 + 2 * (k + 2) * copies) := by
  simp only [centerCount, all_centers, Set.toFinset_univ, Finset.card_univ]
  change Fintype.card (Point k ⊕ (Bool ⊕ (Label k × Fin copies))) = _
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]

private def paired (k : ℕ) : Fin (k + 2) ↪ Point k :=
  ⟨fun i => ((false, i), (true, i)), fun _ _ h => congrArg (fun p : Point k => p.1.2) h⟩

private def chosen (k copies : ℕ) : Finset (Vertex k copies) :=
  (Finset.univ.map (paired k)).disjSum (Finset.univ.map Function.Embedding.inl)

private theorem paired_mem (k copies : ℕ) (i : Fin (k + 2)) :
    Sum.inl (paired k i) ∈ chosen k copies := by
  exact Finset.inl_mem_disjSum.mpr (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private theorem large_mem (k copies : ℕ) (b : Bool) :
    Sum.inr (.inl b) ∈ chosen k copies := by
  exact Finset.inr_mem_disjSum.mpr (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)

theorem domination_le (k copies : ℕ) :
    (graph k copies).totalDominationNumber ≤ k + 2 + 2 := by
  apply Nat.sInf_le
  refine ⟨chosen k copies, ⟨?_, by
    simp [chosen, Finset.card_disjSum]⟩⟩
  intro v
  rcases v with p | b
  · rcases covered_by_large p with h | h
    · exact ⟨.inr (.inl false), large_mem k copies false, h⟩
    · exact ⟨.inr (.inl true), large_mem k copies true, h⟩
  · rcases b with b | ⟨⟨bit, i⟩, r⟩
    · exact ⟨.inl (paired k 0), paired_mem k copies 0, avoids_omission rfl b⟩
    · refine ⟨.inl (paired k i), paired_mem k copies i, ?_⟩
      cases bit
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem degree_point_le {k copies : ℕ} (p : Point k) :
    (graph k copies).degree (.inl p) ≤ 2 * copies + 2 := by
  let labels : Finset (Label k) := {p.1, p.2}
  let blocks : Finset (Block k copies) := Finset.univ.disjSum (labels ×ˢ Finset.univ)
  have hm : (graph k copies).neighborFinset (.inl p) ⊆ blocks.map Function.Embedding.inr := by
    intro v hv
    rw [mem_neighborFinset] at hv
    rcases v with q | b
    · exact hv.elim
    · apply Finset.mem_map.mpr
      refine ⟨b, ?_, rfl⟩
      rcases b with b | ⟨i, r⟩
      · exact Finset.inl_mem_disjSum.mpr (Finset.mem_univ _)
      · have hr : p.1 = i ∨ p.2 = i := hv
        exact Finset.inr_mem_disjSum.mpr (Finset.mem_product.mpr
          ⟨by simpa only [labels, Finset.mem_insert, Finset.mem_singleton, eq_comm] using hr,
            Finset.mem_univ _⟩)
  calc
    _ ≤ (blocks.map Function.Embedding.inr).card := by
      rw [← card_neighborFinset_eq_degree]
      exact Finset.card_le_card hm
    _ = 2 + labels.card * copies := by
      simp [blocks, Finset.card_disjSum, Finset.card_product]
    _ ≤ _ := by
      have h : labels.card * copies ≤ 2 * copies :=
        Nat.mul_le_mul_right copies (pair_card_le p.1 p.2)
      omega

private theorem degree_block_le {k copies : ℕ} (b : Block k copies) :
    (graph k copies).degree (.inr b) ≤ (2 * (k + 2)) * (2 * (k + 2)) := by
  have hm : (graph k copies).neighborFinset (.inr b) ⊆
      (Finset.univ : Finset (Point k)).map Function.Embedding.inl := by
    intro v hv
    rw [mem_neighborFinset] at hv
    rcases v with p | b'
    · exact Finset.mem_map.mpr ⟨p, Finset.mem_univ _, rfl⟩
    · exact hv.elim
  rw [← card_neighborFinset_eq_degree]
  simpa only [Finset.card_map, Finset.card_univ, point_card] using Finset.card_le_card hm

theorem max_edge_neighborhood_le (k copies : ℕ) : edgeNeighborhoodMax (graph k copies) ≤
    2 * copies + 2 + (2 * (k + 2)) * (2 * (k + 2)) := by
  apply Finset.sup_le_iff.mpr
  rintro ⟨u, v⟩ he
  have hadj := (Finset.mem_filter.mp he).2
  refine (Finset.card_union_le _ _).trans ?_
  simp only [card_neighborFinset_eq_degree]
  rcases u with p | a <;> rcases v with q | b
  · exact hadj.elim
  · exact Nat.add_le_add (degree_point_le p) (degree_block_le b)
  · rw [Nat.add_comm]
    exact Nat.add_le_add (degree_point_le q) (degree_block_le a)
  · exact hadj.elim

theorem max_edge_neighborhood_pos (k copies : ℕ) : 0 < edgeNeighborhoodMax (graph k copies) :=
  edgeNeighborhoodMax_pos_of_edge (graph k copies) (u := .inl (paired k 0))
    (v := .inr (.inl false)) (avoids_omission rfl false)

end WOWII255.PairFamily
