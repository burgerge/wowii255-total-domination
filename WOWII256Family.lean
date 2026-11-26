import WOWII256
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! 第 256 题的参数化二分图。左右两侧均保留最小度点。 -/

namespace WOWII256.Family

open SimpleGraph
open WOWII255 (incidenceGraph edgeNeighborhoodMax edgeNeighborhoodMax_pos_of_edge)

abbrev Left (k m : ℕ) := Fin k × Bool × Fin m
abbrev Ordinary (k m : ℕ) := Fin k × Fin m × Fin m
abbrev Right (k m : ℕ) := Option (Ordinary k m)
abbrev Vertex (k m : ℕ) := Left k m ⊕ Right k m

private def relation {k m : ℕ} (p : Left k m) : Right k m → Prop
  | none => True
  | some a => p.1 = a.1 ∧ (p.2.1 = false ∨ p.2.2 = a.2.1)

private instance {k m : ℕ} : DecidableRel (@relation k m) := by
  intro p a
  cases a <;> unfold relation <;> infer_instance

def graph (k m : ℕ) : SimpleGraph (Vertex k m) := incidenceGraph relation

instance (k m : ℕ) : DecidableRel (graph k m).Adj :=
  inferInstanceAs (DecidableRel (incidenceGraph (@relation k m)).Adj)

variable {k m : ℕ}

private abbrev left (g : Fin k) (batch : Bool) (j : Fin m) : Vertex k m :=
  .inl (g, batch, j)

private abbrev right (g : Fin k) (b j : Fin m) : Vertex k m :=
  .inr (some (g, b, j))

private abbrev hub (k m : ℕ) : Vertex k m := .inr none

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

private theorem degree_eq_card_of_embedding {α : Type} [Fintype α] (v : Vertex k m)
    (f : α ↪ Vertex k m) (hn : ∀ a, (graph k m).Adj v (f a))
    (hc : ∀ w, (graph k m).Adj v w → ∃ a, f a = w) :
    (graph k m).degree v = Fintype.card α := by
  have h : (graph k m).neighborFinset v = Finset.univ.map f := by
    ext w
    rw [mem_neighborFinset, Finset.mem_map]
    exact ⟨fun h => let ⟨a, ha⟩ := hc w h; ⟨a, Finset.mem_univ _, ha⟩,
      fun ⟨a, _, ha⟩ => ha ▸ hn a⟩
  rw [← card_neighborFinset_eq_degree, h, Finset.card_map, Finset.card_univ]

private def originalNeighbors (g : Fin k) (m : ℕ) : Option (Fin m × Fin m) ↪ Vertex k m where
  toFun
    | none => hub k m
    | some (b, j) => right g b j
  inj' u v h := by
    cases u <;> cases v <;> simp_all

private def batchNeighbors (g : Fin k) (b : Fin m) : Option (Fin m) ↪ Vertex k m where
  toFun
    | none => hub k m
    | some j => right g b j
  inj' u v h := by
    cases u <;> cases v <;> simp_all

private def rightNeighbors (g : Fin k) (b : Fin m) : Option (Fin m) ↪ Vertex k m where
  toFun
    | none => left g true b
    | some j => left g false j
  inj' u v h := by
    cases u <;> cases v <;> simp_all

private theorem degree_original (g : Fin k) (i : Fin m) :
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

private theorem degree_batch (g : Fin k) (b : Fin m) :
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

private theorem degree_right (g : Fin k) (b j : Fin m) :
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

private theorem degree_hub (k m : ℕ) : (graph k m).degree (hub k m) = 2 * k * m := by
  have h := degree_eq_card_of_embedding (hub k m) Function.Embedding.inl
    (fun _ => trivial) (by rintro (p | p) h <;> first | exact ⟨p, rfl⟩ | exact h.elim)
  simpa [Fintype.card_prod, mul_comm, mul_left_comm] using h

private theorem degree_hub_lower (hk : 1 ≤ k) (hm : 1 ≤ m) : m + 1 ≤ 2 * k * m := by
  have h := Nat.mul_le_mul_right m (show 2 ≤ 2 * k by omega)
  omega

private theorem degree_lower (hk : 1 ≤ k) (hm : 1 ≤ m) (v : Vertex k m) :
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

private theorem all_targets (hk : 1 ≤ k) (hm : 1 ≤ m) :
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

private def chosenEmbedding (m : ℕ) [NeZero m] : Fin k ↪ Vertex k m :=
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
