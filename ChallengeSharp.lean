module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Sum
public import Mathlib.Tactic

@[expose] public section

/-!
本文件包含完全证明。两条最小阶定理或两题的锐性定理共用同一套定义。

总支配数定义沿用 Formal Conjectures 的 Apache-2.0 源码
FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Domination.lean，
提交 9097e2f90e66d2f6244209cb1c07f7120d17ec53。
-/

namespace SimpleGraph

variable {α : Type*} {G : SimpleGraph α}

/-- A set `D` is a total dominating set if every vertex is adjacent to a vertex
in `D`. -/
def IsTotalDominating (G : SimpleGraph α) (D : Set α) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

/-- An `n`-total dominating set is a total dominating set with `n` vertices. -/
@[mk_iff]
structure IsTotalNDominatingSet (n : ℕ) (D : Finset α) : Prop where
  isTotalDominating : G.IsTotalDominating D
  card_eq : D.card = n

/-- The total domination number of `G`. -/
noncomputable def totalDominationNumber (G : SimpleGraph α) : ℕ :=
  sInf {n | ∃ D : Finset α, G.IsTotalNDominatingSet n D}

end SimpleGraph

namespace WOWII255

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 第 28 号定义中的边邻域。对端点的次序取两次不会改变最大值。 -/
def edgeNeighborhoodMax (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun e : V × V => G.Adj e.1 e.2)).sup
    (fun e => (G.neighborFinset e.1 ∪ G.neighborFinset e.2).card)

/-- 第 64 号定义中的图中心的基数。 -/
noncomputable def centerCount (G : SimpleGraph V) : ℕ := by
  classical
  exact G.center.toFinset.card

/-- 第 255 题原不等式，使用实数除法。 -/
def Bound (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (2 * (centerCount G : ℝ)) / (edgeNeighborhoodMax G : ℝ) ≤ G.totalDominationNumber

end WOWII255

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax)

section

variable {V : Type*} [Fintype V]

/-- 最小度顶点集合的开邻域。 -/
def minDegreeNeighborhood (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter (fun v => ∃ u, G.Adj v u ∧ ∀ w, G.degree u ≤ G.degree w)

/-- 在原题第 256 题中，分子为最小度顶点集合的开邻域的基数。 -/
def Bound (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] : Prop :=
  2 * ((minDegreeNeighborhood G).card : ℝ) / (edgeNeighborhoodMax G : ℝ) ≤ G.totalDominationNumber

end

end WOWII256

/-! 二分关联图的距离判据，以及总支配数的通用覆盖下界。 -/

namespace WOWII255

open SimpleGraph

section Incidence

variable {P B : Type*} (R : P → B → Prop)

def incidenceAdj : P ⊕ B → P ⊕ B → Prop
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

theorem walk_two {G : SimpleGraph (P ⊕ B)} {u v w : P ⊕ B}
    (h₁ : G.Adj u v) (h₂ : G.Adj v w) : ∃ p : G.Walk u w, p.length ≤ 3 :=
  ⟨.cons h₁ (.cons h₂ .nil), by simp⟩

theorem walk_three {G : SimpleGraph (P ⊕ B)} {u v w z : P ⊕ B}
    (h₁ : G.Adj u v) (h₂ : G.Adj v w) (h₃ : G.Adj w z) :
    ∃ p : G.Walk u z, p.length ≤ 3 :=
  ⟨.cons h₁ (.cons h₂ (.cons h₃ .nil)), by simp⟩

theorem incidence_short_walk
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

theorem opposite_nonadjacent_far (p : P) (b : B) (h : ¬ R p b) :
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
      rw [SimpleGraph.edist_comm] at h
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

/-! 用标签的有序对构造中心为全体顶点的二分图。 -/

namespace WOWII255.PairFamily

open SimpleGraph

abbrev Label (k : ℕ) := Bool × Fin (k + 2)
abbrev Point (k : ℕ) := Label k × Label k
abbrev Block (k copies : ℕ) := Bool ⊕ (Label k × Fin copies)
abbrev Vertex (k copies : ℕ) := Point k ⊕ Block k copies

def fixed (k : ℕ) (b : Bool) : Label k := (b, 0)

def omitted (k : ℕ) (b : Bool) : Point k := (fixed k b, fixed k false)

theorem omitted_ne (k : ℕ) : omitted k false ≠ omitted k true := by
  intro h
  have hbit := congrArg (fun p : Point k => p.1.1) h
  simp [omitted, fixed] at hbit

theorem avoids_omission {k : ℕ} {p : Point k} (h : p.2.1 = true) (b : Bool) :
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

theorem covered_by_large {k : ℕ} (p : Point k) :
    p ≠ omitted k false ∨ p ≠ omitted k true := by
  by_cases h : p = omitted k false
  · exact Or.inr (h ▸ omitted_ne k)
  · exact Or.inl h

theorem points_share_block {k copies : ℕ} [NeZero copies] (p q : Point k) :
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

theorem blocks_share_point {k copies : ℕ} (a b : Block k copies) :
    ∃ p : Point k, relation p a ∧ relation p b := by
  rcases a with a | ⟨i, r⟩ <;> rcases b with b | ⟨j, s⟩
  · exact ⟨(fixed k true, fixed k true), avoids_omission rfl a, avoids_omission rfl b⟩
  · exact ⟨(j, fixed k true), avoids_omission rfl a, Or.inl rfl⟩
  · exact ⟨(i, fixed k true), Or.inl rfl, avoids_omission rfl b⟩
  · exact ⟨(i, j), Or.inl rfl, Or.inr rfl⟩

theorem label_card (k : ℕ) : Fintype.card (Label k) = 2 * (k + 2) := by
  simp [Label, Fintype.card_prod, Fintype.card_bool]

theorem point_card (k : ℕ) :
    Fintype.card (Point k) = (2 * (k + 2)) * (2 * (k + 2)) := by
  rw [Fintype.card_prod, label_card]

theorem pair_card_le {α : Type*} [DecidableEq α] (u v : α) :
    ({u, v} : Finset α).card ≤ 2 := by
  calc
    _ ≤ ({v} : Finset α).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

theorem point_misses_block {k copies : ℕ} [NeZero copies] (p : Point k) :
    ∃ b : Block k copies, ¬ relation p b := by
  have hcard : ({p.1, p.2} : Finset (Label k)).card <
      (Finset.univ : Finset (Label k)).card := by
    rw [Finset.card_univ, label_card]
    exact (pair_card_le _ _).trans_lt (by omega)
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨.inr (i, 0), by simpa [relation, eq_comm] using hi⟩

theorem block_misses_point {k copies : ℕ} (b : Block k copies) :
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

def paired (k : ℕ) : Fin (k + 2) ↪ Point k :=
  ⟨fun i => ((false, i), (true, i)), fun _ _ h => congrArg (fun p : Point k => p.1.2) h⟩

def chosen (k copies : ℕ) : Finset (Vertex k copies) :=
  (Finset.univ.map (paired k)).disjSum (Finset.univ.map Function.Embedding.inl)

theorem paired_mem (k copies : ℕ) (i : Fin (k + 2)) :
    Sum.inl (paired k i) ∈ chosen k copies := by
  exact Finset.inl_mem_disjSum.mpr (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)

theorem large_mem (k copies : ℕ) (b : Bool) :
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

theorem degree_point_le {k copies : ℕ} (p : Point k) :
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

theorem degree_block_le {k copies : ℕ} (b : Block k copies) :
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

/-! 第 255 题中通用系数恰为所有不超过 1 的实数。 -/

namespace WOWII255

open SimpleGraph

/-- 用参数 `c` 代替原猜想中的常数 2。 -/
def CoefficientBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  (c * (centerCount G : ℝ)) / (edgeNeighborhoodMax G : ℝ) ≤ G.totalDominationNumber

theorem coefficient_two_is_original {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : CoefficientBound G 2 ↔ Bound G := Iff.rfl

/-- 量化所有有限连通简单图。非平凡性使分母有意义。 -/
def ValidCoefficient (c : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → CoefficientBound G c

theorem coefficient_valid_of_le_one {c : ℝ} (hc : c ≤ 1) : ValidCoefficient c := by
  intro V _ _ _ G _ hG
  have hadj := hG.preconnected.exists_adj_of_nontrivial
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨v, hv⟩ := hadj u
  have hM : (0 : ℝ) < edgeNeighborhoodMax G :=
    by exact_mod_cast edgeNeighborhoodMax_pos_of_edge G hv
  unfold CoefficientBound
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ 1 * (centerCount G : ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by
      rw [one_mul]
      exact_mod_cast (centerCount_le_order G).trans (order_le_totalDomination_mul_max G hadj)

theorem numerator_le (n extra : ℕ) (hn : 2 ≤ n) :
    (n + 2) * (2 * (n * extra) + extra) ≤ (2 * n + 6) * (n * extra) := by
  calc
    _ = (2 * n * n + 5 * n + 2) * extra := by ring
    _ ≤ (2 * n * n + 6 * n) * extra := Nat.mul_le_mul_right extra (by omega)
    _ = _ := by ring

/-- 对每个实数 `c > 1` 给出解析构造的反例。 -/
theorem exists_pair_counterexample {c : ℝ} (hc : 1 < c) :
    ∃ k copies : ℕ, 0 < copies ∧ (PairFamily.graph k copies).Connected ∧
      0 < edgeNeighborhoodMax (PairFamily.graph k copies) ∧
      ¬ CoefficientBound (PairFamily.graph k copies) c := by
  obtain ⟨k, hk⟩ := exists_nat_gt (3 / (c - 1))
  let n := k + 2
  let extra := 2 + (2 * n) * (2 * n)
  let copies := n * extra
  let G := PairFamily.graph k copies
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hcopies : 0 < copies := by dsimp [copies, n, extra]; positivity
  let _ : NeZero copies := ⟨Nat.ne_of_gt hcopies⟩
  have hM : 0 < edgeNeighborhoodMax G := PairFamily.max_edge_neighborhood_pos k copies
  refine ⟨k, copies, hcopies, PairFamily.connected k copies, hM, ?_⟩
  have hg : G.totalDominationNumber ≤ n + 2 := PairFamily.domination_le k copies
  have hm : edgeNeighborhoodMax G ≤ 2 * copies + extra := by
    simpa only [G, n, extra, Nat.add_assoc] using PairFamily.max_edge_neighborhood_le k copies
  have hz : 2 * n * copies ≤ centerCount G := by
    change 2 * n * copies ≤ centerCount (PairFamily.graph k copies)
    rw [PairFamily.center_count]
    change 2 * n * copies ≤ (2 * n) * (2 * n) + (2 + 2 * n * copies)
    omega
  have hmuld : G.totalDominationNumber * edgeNeighborhoodMax G ≤ (2 * n + 6) * copies :=
    (Nat.mul_le_mul hg hm).trans (numerator_le n extra hn)
  have hk' : 3 < (k : ℝ) * (c - 1) := (div_lt_iff₀ (sub_pos.mpr hc)).mp hk
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast (Nat.le_add_right k 2)
  have hnc : 3 < (n : ℝ) * (c - 1) :=
    hk'.trans_le (mul_le_mul_of_nonneg_right hkn (sub_nonneg.mpr hc.le))
  have hcompare : 2 * (n : ℝ) + 6 < c * (2 * (n : ℝ)) := by nlinarith only [hnc]
  have hcpos : 0 ≤ c := by linarith
  show ¬ CoefficientBound G c
  intro h
  unfold CoefficientBound at h
  have hcond := (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < edgeNeighborhoodMax G)).mp h
  have hmuldr : (G.totalDominationNumber : ℝ) * edgeNeighborhoodMax G ≤
      (2 * (n : ℝ) + 6) * copies := by exact_mod_cast hmuld
  have hzreal : 2 * (n : ℝ) * copies ≤ centerCount G := by exact_mod_cast hz
  have hstrict : (2 * (n : ℝ) + 6) * copies < c * (centerCount G : ℝ) := by
    calc
      _ < (c * (2 * (n : ℝ))) * copies :=
        mul_lt_mul_of_pos_right hcompare (by exact_mod_cast hcopies)
      _ = c * (2 * (n : ℝ) * copies) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hzreal hcpos
  exact (hstrict.trans_le (hcond.trans hmuldr)).false

/-- 必要与充分条件。通用不等式的最大实数系数为 1。 -/
theorem sharp_coefficient (c : ℝ) : ValidCoefficient c ↔ c ≤ 1 := by
  refine ⟨?_, coefficient_valid_of_le_one⟩
  intro h
  by_contra! hc
  obtain ⟨k, m, _, hconn, _, hbad⟩ := exists_pair_counterexample hc
  have : Nontrivial (PairFamily.Vertex k m) :=
    ⟨⟨.inr (.inl false), .inr (.inl true), by simp⟩⟩
  exact hbad (h (PairFamily.graph k m) hconn)

-- 基例检查顶点计数和端点。集成检查排除原猜想使用的系数 2。
example : centerCount (PairFamily.graph 0 1) = 22 := by
  rw [PairFamily.center_count]

example : ValidCoefficient 1 := (sharp_coefficient 1).mpr le_rfl

example : ¬ ValidCoefficient 2 := by
  intro h
  have := (sharp_coefficient 2).mp h
  norm_num at this


end WOWII255

/-! 第 256 题的参数化二分图。左右两侧均保留最小度点。 -/

namespace WOWII256.Family

open SimpleGraph
open WOWII255 (incidenceGraph edgeNeighborhoodMax edgeNeighborhoodMax_pos_of_edge)

abbrev Left (k m : ℕ) := Fin k × Bool × Fin m
abbrev Ordinary (k m : ℕ) := Fin k × Fin m × Fin m
abbrev Right (k m : ℕ) := Option (Ordinary k m)
abbrev Vertex (k m : ℕ) := Left k m ⊕ Right k m

def relation {k m : ℕ} (p : Left k m) : Right k m → Prop
  | none => True
  | some a => p.1 = a.1 ∧ (p.2.1 = false ∨ p.2.2 = a.2.1)

instance {k m : ℕ} : DecidableRel (@relation k m) := by
  intro p a
  cases a <;> unfold relation <;> infer_instance

def graph (k m : ℕ) : SimpleGraph (Vertex k m) := incidenceGraph relation

instance (k m : ℕ) : DecidableRel (graph k m).Adj :=
  inferInstanceAs (DecidableRel (incidenceGraph (@relation k m)).Adj)

variable {k m : ℕ}

abbrev left (g : Fin k) (batch : Bool) (j : Fin m) : Vertex k m :=
  .inl (g, batch, j)

abbrev right (g : Fin k) (b j : Fin m) : Vertex k m :=
  .inr (some (g, b, j))

abbrev hub (k m : ℕ) : Vertex k m := .inr none

theorem connected (k m : ℕ) : (graph k m).Connected := by
  have hreach (v : Vertex k m) : (graph k m).Reachable v (hub k m) := by
    rcases v with p | (_ | ⟨g, b, j⟩)
    · have hp : (graph k m).Adj (.inl p) (hub k m) := trivial
      exact ⟨hp.toWalk⟩
    · exact ⟨.nil⟩
    · have hp : (graph k m).Adj (right g b j) (left g false j) := by simp [graph, relation]
      have hz : (graph k m).Adj (left g false j) (hub k m) := trivial
      exact ⟨.cons hp hz.toWalk⟩
  refine { preconnected := ?_, nonempty := ⟨hub k m⟩ }
  intro v w
  exact (hreach v).trans (hreach w).symm

theorem bipartite (k m : ℕ) : (graph k m).IsBipartite := by
  refine ⟨Coloring.mk (Sum.elim (fun _ => 0) (fun _ => 1) : Vertex k m → Fin 2) ?_⟩
  intro u v h
  cases u <;> cases v <;> simp [graph] at h ⊢

theorem degree_eq_card_of_embedding {α : Type} [Fintype α] (v : Vertex k m)
    (f : α ↪ Vertex k m) (hn : ∀ a, (graph k m).Adj v (f a))
    (hc : ∀ w, (graph k m).Adj v w → ∃ a, f a = w) :
    (graph k m).degree v = Fintype.card α := by
  have h : (graph k m).neighborFinset v = Finset.univ.map f := by
    ext w
    rw [mem_neighborFinset, Finset.mem_map]
    exact ⟨fun h => let ⟨a, ha⟩ := hc w h; ⟨a, Finset.mem_univ _, ha⟩,
      fun ⟨a, _, ha⟩ => ha ▸ hn a⟩
  rw [← card_neighborFinset_eq_degree, h, Finset.card_map, Finset.card_univ]

def originalNeighbors (g : Fin k) (m : ℕ) : Option (Fin m × Fin m) ↪ Vertex k m where
  toFun
    | none => hub k m
    | some (b, j) => right g b j
  inj' u v h := by
    cases u <;> cases v <;> simp_all

def batchNeighbors (g : Fin k) (b : Fin m) : Option (Fin m) ↪ Vertex k m where
  toFun
    | none => hub k m
    | some j => right g b j
  inj' u v h := by
    cases u <;> cases v <;> simp_all

def rightNeighbors (g : Fin k) (b : Fin m) : Option (Fin m) ↪ Vertex k m where
  toFun
    | none => left g true b
    | some j => left g false j
  inj' u v h := by
    cases u <;> cases v <;> simp_all

theorem degree_original (g : Fin k) (i : Fin m) :
    (graph k m).degree (left g false i) = m * m + 1 := by
  have h := degree_eq_card_of_embedding (left g false i) (originalNeighbors g m)
    (by
      rintro (_ | ⟨b, j⟩)
      · exact trivial
      · exact ⟨rfl, Or.inl rfl⟩)
    (by
      rintro (p | (_ | ⟨h, b, j⟩)) ha
      · exact ha.elim
      · exact ⟨none, rfl⟩
      · have hg : g = h := by simpa [graph, relation] using ha
        subst h
        exact ⟨some (b, j), rfl⟩)
  simpa [Fintype.card_prod] using h

theorem degree_batch (g : Fin k) (b : Fin m) :
    (graph k m).degree (left g true b) = m + 1 := by
  have h := degree_eq_card_of_embedding (left g true b) (batchNeighbors g b)
    (by
      rintro (_ | j)
      · exact trivial
      · exact ⟨rfl, Or.inr rfl⟩)
    (by
      rintro (p | (_ | ⟨h, c, j⟩)) ha
      · exact ha.elim
      · exact ⟨none, rfl⟩
      · have hgb : g = h ∧ b = c := by simpa [graph, relation] using ha
        obtain ⟨rfl, rfl⟩ := hgb
        exact ⟨some j, rfl⟩)
  simpa using h

theorem degree_right (g : Fin k) (b j : Fin m) :
    (graph k m).degree (right g b j) = m + 1 := by
  have h := degree_eq_card_of_embedding (right g b j) (rightNeighbors g b)
    (by
      rintro (_ | i)
      · exact ⟨rfl, Or.inr rfl⟩
      · exact ⟨rfl, Or.inl rfl⟩)
    (by
      rintro (⟨a, flag, i⟩ | p) ha
      · have hgi : a = g ∧ (flag = false ∨ i = b) := ha
        obtain ⟨rfl, hi⟩ := hgi
        cases flag
        · exact ⟨some i, rfl⟩
        · have hi' : i = b := by simpa using hi
          subst i
          exact ⟨none, rfl⟩
      · exact ha.elim)
  simpa using h

theorem degree_hub (k m : ℕ) : (graph k m).degree (hub k m) = 2 * k * m := by
  have h := degree_eq_card_of_embedding (hub k m) Function.Embedding.inl
    (fun _ => trivial) (by rintro (p | p) h <;> first | exact ⟨p, rfl⟩ | exact h.elim)
  simpa [Fintype.card_prod, mul_comm, mul_left_comm] using h

theorem degree_hub_lower (hk : 1 ≤ k) (hm : 1 ≤ m) : m + 1 ≤ 2 * k * m := by
  have h := Nat.mul_le_mul_right m (show 2 ≤ 2 * k by omega)
  omega

theorem degree_lower (hk : 1 ≤ k) (hm : 1 ≤ m) (v : Vertex k m) :
    m + 1 ≤ (graph k m).degree v := by
  rcases v with ⟨g, flag, i⟩ | (_ | ⟨g, b, j⟩)
  · cases flag
    · rw [degree_original]
      have h := Nat.mul_le_mul_left m hm
      omega
    · rw [degree_batch]
  · rw [degree_hub]
    exact degree_hub_lower hk hm
  · rw [degree_right]

theorem all_targets (hk : 1 ≤ k) (hm : 1 ≤ m) :
    minDegreeNeighborhood (graph k m) = Finset.univ := by
  let _ : NeZero k := ⟨by omega⟩
  let _ : NeZero m := ⟨by omega⟩
  apply Finset.eq_univ_of_forall
  intro v
  simp only [minDegreeNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and]
  suffices h : ∃ w, (graph k m).Adj v w ∧ (graph k m).degree w = m + 1 by
    obtain ⟨w, hvw, hd⟩ := h
    exact ⟨w, hvw, fun u => hd ▸ degree_lower hk hm u⟩
  rcases v with ⟨g, flag, i⟩ | (_ | ⟨g, b, j⟩)
  · exact ⟨right g i i, by simp [graph, relation], degree_right g i i⟩
  · exact ⟨left 0 true 0, trivial, degree_batch 0 0⟩
  · exact ⟨left g true b, by simp [graph, relation], degree_batch g b⟩

theorem target_card_lower (hk : 1 ≤ k) (hm : 1 ≤ m) :
    k * (m * m) ≤ (minDegreeNeighborhood (graph k m)).card := by
  rw [all_targets hk hm, Finset.card_univ]
  simp only [Vertex, Left, Right, Ordinary, Fintype.card_sum, Fintype.card_option,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

def chosenEmbedding (m : ℕ) [NeZero m] : Fin k ↪ Vertex k m :=
  ⟨fun g => left g false 0, fun _ _ h => by simpa using h⟩

theorem domination_le (k m : ℕ) [NeZero k] [NeZero m] :
    (graph k m).totalDominationNumber ≤ k + 1 := by
  let D := insert (hub k m) (Finset.univ.map (chosenEmbedding m))
  have hhub : hub k m ∉ (Finset.univ.map (chosenEmbedding m)) := by
    simp [chosenEmbedding]
  apply Nat.sInf_le
  refine ⟨D, ⟨?_, by simp [D, Finset.card_insert_of_notMem hhub]⟩⟩
  have hp (g : Fin k) : left g false 0 ∈ D :=
    Finset.mem_insert_of_mem (Finset.mem_map.mpr ⟨g, Finset.mem_univ _, rfl⟩)
  rintro (p | (_ | ⟨g, b, j⟩))
  · exact ⟨hub k m, Finset.mem_insert_self _ _, trivial⟩
  · exact ⟨left 0 false 0, hp 0, trivial⟩
  · exact ⟨left g false 0, hp g, by simp [graph, relation]⟩

theorem maximum_le (hk : 1 ≤ k) (hm : 1 ≤ m) :
    edgeNeighborhoodMax (graph k m) ≤ m * m + 1 + 2 * k * m := by
  have hl (u : Left k m) : (graph k m).degree (.inl u) ≤ m * m + 1 := by
    obtain ⟨g, flag, i⟩ := u
    cases flag
    · rw [degree_original]
    · rw [degree_batch]
      have h := Nat.mul_le_mul_left m hm
      omega
  have hr (v : Right k m) : (graph k m).degree (.inr v) ≤ 2 * k * m := by
    rcases v with _ | ⟨g, b, j⟩
    · rw [degree_hub]
    · rw [degree_right]
      exact degree_hub_lower hk hm
  apply Finset.sup_le_iff.mpr
  rintro ⟨u, v⟩ he
  have hadj := (Finset.mem_filter.mp he).2
  refine (Finset.card_union_le _ _).trans ?_
  simp only [card_neighborFinset_eq_degree]
  rcases u with p | a <;> rcases v with q | b
  · exact hadj.elim
  · simpa only [Nat.mul_assoc] using Nat.add_le_add (hl p) (hr b)
  · rw [Nat.add_comm]
    simpa only [Nat.mul_assoc] using Nat.add_le_add (hl q) (hr a)
  · exact hadj.elim

theorem maximum_pos (k m : ℕ) [NeZero k] [NeZero m] : 0 < edgeNeighborhoodMax (graph k m) :=
  edgeNeighborhoodMax_pos_of_edge (graph k m) (u := left 0 false 0) (v := hub k m) trivial

end WOWII256.Family

/-! 第 256 题的最优普适系数，包括限制为二分图的情形。 -/

namespace WOWII256

open SimpleGraph
open WOWII255 (edgeNeighborhoodMax edgeNeighborhoodMax_pos_of_edge order_le_totalDomination_mul_max)

/-- 将原猜想右侧的系数 2 替换成 c。 -/
def CoefficientBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  c * ((minDegreeNeighborhood G).card : ℝ) / (edgeNeighborhoodMax G : ℝ) ≤
    G.totalDominationNumber

theorem coefficient_two_is_original {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : CoefficientBound G 2 ↔ Bound G := Iff.rfl

/-- 有限连通简单图上的有效系数。 -/
def ValidCoefficient (c : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → CoefficientBound G c

/-- 限制为连通二分图时的有效系数。 -/
def BipartiteValidCoefficient (c : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.Connected → G.IsBipartite → CoefficientBound G c

theorem coefficient_valid_of_le_one {c : ℝ} (hc : c ≤ 1) : ValidCoefficient c := by
  intro V _ _ _ G _ hG
  have hadj := hG.preconnected.exists_adj_of_nontrivial
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨v, hv⟩ := hadj u
  have hM : (0 : ℝ) < edgeNeighborhoodMax G :=
    by exact_mod_cast edgeNeighborhoodMax_pos_of_edge G hv
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ 1 * ((minDegreeNeighborhood G).card : ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by
      rw [one_mul]
      exact_mod_cast ((Finset.card_le_univ (minDegreeNeighborhood G)).trans
        (order_le_totalDomination_mul_max G hadj))

theorem estimate (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : m = k * k) :
    (k + 1) * (m * m + 1 + 2 * k * m) ≤ (k + 7) * (m * m) := by
  have hm₁ : 1 ≤ m := by
    rw [hm]
    exact Nat.mul_pos (by omega) (by omega)
  have h1 : m * m + 1 + 2 * k * m ≤ m * m + 3 * k * m := by
    have hkm := Nat.mul_le_mul_right m hk
    calc
      _ ≤ m * m + k * m + 2 * k * m := by omega
      _ = _ := by ring
  have h2 : (k + 1) * (3 * k * m) ≤ 6 * (m * m) := by
    calc
      _ ≤ (2 * k) * (3 * k * m) := Nat.mul_le_mul_right _ (by omega)
      _ = 6 * ((k * k) * m) := by ring
      _ = _ := by rw [← hm]
  calc
    _ ≤ (k + 1) * (m * m + 3 * k * m) := Nat.mul_le_mul_left _ h1
    _ = (k + 1) * (m * m) + (k + 1) * (3 * k * m) := by ring
    _ ≤ (k + 1) * (m * m) + 6 * (m * m) := Nat.add_le_add_left h2 _
    _ = _ := by ring

/-- 任意大于 1 的系数都存在参数化的连通二分图反例。 -/
theorem exists_bipartite_counterexample {c : ℝ} (hc : 1 < c) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ (Family.graph k m).Connected ∧
      (Family.graph k m).IsBipartite ∧ ¬ CoefficientBound (Family.graph k m) c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (7 / (c - 1))
  let k := n + 2
  let m := k * k
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hm : 1 ≤ m := Nat.mul_pos (by omega) (by omega)
  let _ : NeZero k := ⟨by omega⟩
  let _ : NeZero m := ⟨by omega⟩
  let G := Family.graph k m
  refine ⟨k, m, by omega, by omega, Family.connected k m, Family.bipartite k m, ?_⟩
  have hM := Family.maximum_pos k m
  have hgm : G.totalDominationNumber * edgeNeighborhoodMax G ≤ (k + 7) * (m * m) :=
    (Nat.mul_le_mul (Family.domination_le k m) (Family.maximum_le hk hm)).trans (estimate k hk m rfl)
  have hcard := Family.target_card_lower hk hm
  have hn' : 7 < (n : ℝ) * (c - 1) := (div_lt_iff₀ (sub_pos.mpr hc)).mp hn
  have hnk : (n : ℝ) ≤ k := by exact_mod_cast (Nat.le_add_right n 2)
  have hkc : 7 < (k : ℝ) * (c - 1) :=
    hn'.trans_le (mul_le_mul_of_nonneg_right hnk (sub_nonneg.mpr hc.le))
  have hks : (k : ℝ) + 7 < c * k := by nlinarith only [hkc]
  intro hb
  have hb' := (div_le_iff₀ (by exact_mod_cast hM : (0 : ℝ) < edgeNeighborhoodMax G)).mp hb
  have hgm' : (G.totalDominationNumber : ℝ) * edgeNeighborhoodMax G ≤
      ((k : ℝ) + 7) * ((m : ℝ) * m) := by exact_mod_cast hgm
  have hcard' : (k : ℝ) * ((m : ℝ) * m) ≤ (minDegreeNeighborhood G).card := by
    exact_mod_cast hcard
  have hms : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hstrict : ((k : ℝ) + 7) * ((m : ℝ) * m) <
      c * ((minDegreeNeighborhood G).card : ℝ) := by
    calc
      _ < (c * k) * ((m : ℝ) * m) := mul_lt_mul_of_pos_right hks (mul_pos hms hms)
      _ = c * (k * ((m : ℝ) * m)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcard' (by linarith)
  exact (hstrict.trans_le (hb'.trans hgm')).false

/-- 常数 1 在二分图类中已经最优。 -/
theorem sharp_coefficient_bipartite (c : ℝ) : BipartiteValidCoefficient c ↔ c ≤ 1 := by
  constructor
  · intro h
    by_contra! hc
    obtain ⟨k, m, hk, hm, hconn, hbip, hbad⟩ := exists_bipartite_counterexample hc
    let _ : NeZero k := ⟨Nat.ne_of_gt hk⟩
    let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
    let _ : Nontrivial (Family.Vertex k m) :=
      ⟨⟨.inl (0, false, 0), .inr none, by simp⟩⟩
    exact hbad (h (Family.graph k m) hconn hbip)
  · intro hc V _ _ _ G _ hconn _
    exact coefficient_valid_of_le_one hc G hconn

/-- 通用不等式的最大实数系数是 1。 -/
theorem sharp_coefficient (c : ℝ) : ValidCoefficient c ↔ c ≤ 1 := by
  refine ⟨fun h => (sharp_coefficient_bipartite c).mp ?_, coefficient_valid_of_le_one⟩
  intro V _ _ _ G _ hconn _
  exact h G hconn

example : ValidCoefficient 1 := (sharp_coefficient 1).mpr le_rfl
example : ¬ BipartiteValidCoefficient 2 := by simp [sharp_coefficient_bipartite]


end WOWII256

#print axioms WOWII255.sharp_coefficient
#print axioms WOWII256.sharp_coefficient
#print axioms WOWII256.sharp_coefficient_bipartite
