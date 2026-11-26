import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Finset.Sum
import WOWII255Data
import Mathlib.Tactic

/-!
# Written on the Wall II 第 255 题的反例

点线关联来自三阶射影平面。每条线复制十三次，再加两个覆盖所有点的块。
-/

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

private def adj : Vertex → Vertex → Prop
  | .inl p, .inr b => incident p (kind b)
  | .inr b, .inl p => incident p (kind b)
  | _, _ => False

def exampleGraph : SimpleGraph Vertex where
  Adj := adj
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact id⟩

instance : DecidableRel exampleGraph.Adj := by
  intro u v
  cases u <;> cases v <;> unfold exampleGraph adj <;> infer_instance

private theorem walk_two {u v w : Vertex}
    (h₁ : exampleGraph.Adj u v) (h₂ : exampleGraph.Adj v w) :
    ∃ p : exampleGraph.Walk u w, p.length ≤ 3 :=
  ⟨.cons h₁ (.cons h₂ .nil), by simp⟩

private theorem walk_three {u v w z : Vertex}
    (h₁ : exampleGraph.Adj u v) (h₂ : exampleGraph.Adj v w) (h₃ : exampleGraph.Adj w z) :
    ∃ p : exampleGraph.Walk u z, p.length ≤ 3 :=
  ⟨.cons h₁ (.cons h₂ (.cons h₃ .nil)), by simp⟩

private theorem short_walk (u v : Vertex) :
    ∃ w : exampleGraph.Walk u v, w.length ≤ 3 := by
  cases u with
  | inl p =>
    cases v with
    | inl q =>
      obtain ⟨l, hp, hq⟩ := points_share_line p q
      exact walk_two (v := .inr (.inr (l, 0))) hp hq
    | inr b =>
      obtain ⟨q, hq, _⟩ := blocks_share_point (kind b) (kind b)
      obtain ⟨l, hp, hql⟩ := points_share_line p q
      exact walk_three (v := .inr (.inr (l, 0))) (w := .inl q) hp hql hq
  | inr a =>
    cases v with
    | inl q =>
      obtain ⟨p, hp, _⟩ := blocks_share_point (kind a) (kind a)
      obtain ⟨l, hpl, hql⟩ := points_share_line p q
      exact walk_three (v := .inl p) (w := .inr (.inr (l, 0))) hp hpl hql
    | inr b =>
      obtain ⟨p, ha, hb⟩ := blocks_share_point (kind a) (kind b)
      exact walk_two (v := .inl p) ha hb

theorem connected_example : exampleGraph.Connected := by
  refine { preconnected := ?_, nonempty := ⟨.inl 0⟩ }
  intro u v
  exact ⟨(short_walk u v).choose⟩

private theorem opposite_nonadj_edist (p : Point) (b : Block)
    (h : ¬ incident p (kind b)) : 3 ≤ exampleGraph.edist (.inl p) (.inr b) := by
  have he : 2 < exampleGraph.edist (.inl p) (.inr b) := by
    apply two_lt_edist_iff.mpr
    refine ⟨by simp, h, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro w hw
    have hw' := (exampleGraph.mem_commonNeighbors).mp hw
    cases w with
    | inl q => exact hw'.1
    | inr a => exact hw'.2
  exact Order.add_one_le_of_lt he

theorem eccentricity_example (u : Vertex) : exampleGraph.eccent u = 3 := by
  apply le_antisymm
  · apply (eccent_le_iff _ _).mpr
    intro v
    obtain ⟨w, hw⟩ := short_walk u v
    exact w.edist_le.trans (by exact_mod_cast hw)
  · cases u with
    | inl p =>
      obtain ⟨b, hb⟩ := point_misses_block p
      have h := opposite_nonadj_edist p (rep b) (by simpa using hb)
      exact h.trans edist_le_eccent
    | inr b =>
      obtain ⟨p, hp⟩ := block_misses_point (kind b)
      have h := opposite_nonadj_edist p b hp
      rw [edist_comm] at h
      exact h.trans edist_le_eccent

theorem all_vertices_are_centers : exampleGraph.center = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro u
  obtain ⟨v, hv⟩ := exampleGraph.exists_eccent_eq_radius
  exact (exampleGraph.mem_center_iff u).mpr
    ((eccentricity_example u).trans ((eccentricity_example v).symm.trans hv))

theorem center_count_example : centerCount exampleGraph = 184 := by
  simp only [centerCount, all_vertices_are_centers, Set.toFinset_univ, Finset.card_univ]
  norm_num [Vertex, Block, Point, Fintype.card_sum, Fintype.card_prod]

private def chosen : Finset Vertex :=
  (points (.inr 0)).disjSum (Finset.univ.map Function.Embedding.inl)

private theorem chosen_card : chosen.card = 6 := by
  simp only [chosen, Finset.card_disjSum, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rfl

theorem total_domination_le_six : exampleGraph.totalDominationNumber ≤ 6 := by
  apply Nat.sInf_le
  refine ⟨chosen, ⟨?_, chosen_card⟩⟩
  intro v
  cases v with
  | inl p =>
    rcases covered_by_special p with hp | hp
    · exact ⟨.inr (.inl 0), by simp [chosen], hp⟩
    · exact ⟨.inr (.inl 1), by simp [chosen], hp⟩
  | inr b =>
    obtain ⟨p, hp, hb⟩ := blocks_share_point (.inr 0) (kind b)
    exact ⟨.inl p, by simpa [chosen, points] using hp, hb⟩

private theorem degree_point_le (p : Point) : exampleGraph.degree (.inl p) ≤ 54 := by
  let lines := Finset.univ.filter (fun l : Fin 13 => incident p (.inr l))
  let blocks : Finset Block := (Finset.univ : Finset (Fin 2)).disjSum (lines ×ˢ Finset.univ)
  have h : exampleGraph.neighborFinset (.inl p) ⊆ blocks.map Function.Embedding.inr := by
    intro v hv
    rw [mem_neighborFinset] at hv
    cases v with
    | inl q => exact hv.elim
    | inr b =>
      cases b with
      | inl s => simp [blocks]
      | inr lc =>
        change incident p (.inr lc.1) at hv
        simp [blocks, lines, hv]
  rw [← card_neighborFinset_eq_degree]
  simpa [blocks, lines, Finset.card_disjSum, Finset.card_product, line_count]
    using Finset.card_le_card h

private theorem degree_block_le (b : Block) : exampleGraph.degree (.inr b) ≤ 7 := by
  have h : exampleGraph.neighborFinset (.inr b) =
      (points (kind b)).map Function.Embedding.inl := by
    ext v
    rw [mem_neighborFinset]
    cases v <;> simp [exampleGraph, adj, points]
  rw [← card_neighborFinset_eq_degree, h, Finset.card_map]
  exact block_size (kind b)

theorem edge_neighborhood_max_le : edgeNeighborhoodMax exampleGraph ≤ 61 := by
  apply Finset.sup_le_iff.mpr
  rintro ⟨u, v⟩ he
  have hadj := (Finset.mem_filter.mp he).2
  apply (Finset.card_union_le _ _).trans
  simp only [card_neighborFinset_eq_degree]
  cases u with
  | inl p =>
    cases v with
    | inl q => exact hadj.elim
    | inr b => exact Nat.add_le_add (degree_point_le p) (degree_block_le b)
  | inr b =>
    cases v with
    | inl p => exact Nat.add_le_add (degree_block_le b) (degree_point_le p)
    | inr a => exact hadj.elim

private theorem edge_neighborhood_max_pos_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (h : G.Adj u v) : 0 < edgeNeighborhoodMax G := by
  have he : (u, v) ∈ Finset.univ.filter (fun f : V × V => G.Adj f.1 f.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hm : v ∈ G.neighborFinset u := by rwa [mem_neighborFinset]
  have hp : 0 < (G.neighborFinset u ∪ G.neighborFinset v).card :=
    Finset.card_pos.mpr ⟨v, Finset.mem_union_left _ hm⟩
  exact hp.trans_le (Finset.le_sup
    (f := fun e => (G.neighborFinset e.1 ∪ G.neighborFinset e.2).card) he)

theorem edge_neighborhood_max_pos : 0 < edgeNeighborhoodMax exampleGraph :=
  edge_neighborhood_max_pos_of_adj exampleGraph (u := .inl 0) (v := .inr (.inl 0)) rfl

private theorem strict_arithmetic {g m : ℕ} (hg : g ≤ 6) (hm : m ≤ 61) (hm₀ : 0 < m) :
    ¬ 2 * (184 : ℝ) / (m : ℝ) ≤ (g : ℝ) := by
  intro h
  have hm₀' : (0 : ℝ) < m := by exact_mod_cast hm₀
  have hg' : (g : ℝ) ≤ 6 := by exact_mod_cast hg
  have hm' : (m : ℝ) ≤ 61 := by exact_mod_cast hm
  have h₁ := (div_le_iff₀ hm₀').mp h
  have h₂ := mul_le_mul hg' hm' hm₀'.le (by norm_num : (0 : ℝ) ≤ 6)
  linarith

theorem refutes_bound : ¬ Bound exampleGraph := by
  unfold Bound
  rw [center_count_example]
  exact strict_arithmetic total_domination_le_six edge_neighborhood_max_le
    edge_neighborhood_max_pos

/-- 第 255 题的原全称命题为假。反例有边且分母严格为正。 -/
theorem conjecture255_false :
    ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → Bound G) := by
  intro universal
  exact refutes_bound (universal exampleGraph connected_example)

#print axioms conjecture255_false

end WOWII255
