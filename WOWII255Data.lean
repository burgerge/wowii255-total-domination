import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-! 第 255 题反例的点块关联及有限证书。 -/

namespace WOWII255

abbrev Point := Fin 13
abbrev Kind := Fin 2 ⊕ Fin 13
abbrev Block := Fin 2 ⊕ (Fin 13 × Fin 13)
abbrev Vertex := Point ⊕ Block

/-- 第 `p` 位表示编号为 `p` 的点是否在线上，顺序与坐标字典序一致。 -/
private def lineMask : Fin 13 → ℕ :=
  ![1170, 113, 2584, 4372, 15, 4674, 2338, 7169, 1352, 1572, 897, 2244, 4264]

private def blockMask : Kind → ℕ
  | .inl b => if b = 0 then 127 else 8065
  | .inr l => lineMask l

def incident (p : Point) (b : Kind) : Prop := (blockMask b).testBit p.val = true

instance (p : Point) (b : Kind) : Decidable (incident p b) := by
  unfold incident
  infer_instance

def points (b : Kind) : Finset Point := Finset.univ.filter (fun p => incident p b)

def kind : Block → Kind
  | .inl b => .inl b
  | .inr (l, _) => .inr l

def rep : Kind → Block
  | .inl b => .inl b
  | .inr l => .inr (l, 0)

@[simp] theorem kind_rep (b : Kind) : kind (rep b) = b := by
  cases b <;> rfl

private def lineWitness : Point → Point → Fin 13 :=
  ![
    ![1, 4, 4, 4, 1, 1, 1, 10, 10, 10, 7, 7, 7],
    ![4, 0, 4, 4, 0, 6, 5, 0, 6, 5, 0, 6, 5],
    ![4, 4, 3, 4, 3, 9, 11, 11, 3, 9, 9, 11, 3],
    ![4, 4, 4, 2, 2, 12, 8, 12, 8, 2, 8, 2, 12],
    ![1, 0, 3, 2, 0, 1, 1, 0, 3, 2, 0, 2, 3],
    ![1, 6, 9, 12, 1, 1, 1, 12, 6, 9, 9, 6, 12],
    ![1, 5, 11, 8, 1, 1, 1, 11, 8, 5, 8, 11, 5],
    ![10, 0, 11, 12, 0, 12, 11, 0, 10, 10, 0, 11, 12],
    ![10, 6, 3, 8, 3, 6, 8, 10, 3, 10, 8, 6, 3],
    ![10, 5, 9, 2, 2, 9, 5, 10, 10, 2, 9, 2, 5],
    ![7, 0, 9, 8, 0, 9, 8, 0, 8, 9, 0, 7, 7],
    ![7, 6, 11, 2, 2, 6, 11, 11, 6, 2, 7, 2, 7],
    ![7, 5, 3, 12, 3, 12, 5, 12, 3, 5, 7, 7, 3]]

private def commonPointWitness : Fin 15 → Fin 15 → Point :=
  ![
    ![0, 0, 1, 0, 3, 2, 0, 1, 1, 0, 3, 2, 0, 2, 3],
    ![0, 0, 7, 0, 9, 8, 0, 9, 8, 0, 8, 9, 0, 7, 7],
    ![1, 7, 1, 4, 4, 4, 1, 1, 1, 10, 10, 10, 7, 7, 7],
    ![0, 0, 4, 0, 4, 4, 0, 6, 5, 0, 6, 5, 0, 6, 5],
    ![3, 9, 4, 4, 3, 4, 3, 9, 11, 11, 3, 9, 9, 11, 3],
    ![2, 8, 4, 4, 4, 2, 2, 12, 8, 12, 8, 2, 8, 2, 12],
    ![0, 0, 1, 0, 3, 2, 0, 1, 1, 0, 3, 2, 0, 2, 3],
    ![1, 9, 1, 6, 9, 12, 1, 1, 1, 12, 6, 9, 9, 6, 12],
    ![1, 8, 1, 5, 11, 8, 1, 1, 1, 11, 8, 5, 8, 11, 5],
    ![0, 0, 10, 0, 11, 12, 0, 12, 11, 0, 10, 10, 0, 11, 12],
    ![3, 8, 10, 6, 3, 8, 3, 6, 8, 10, 3, 10, 8, 6, 3],
    ![2, 9, 10, 5, 9, 2, 2, 9, 5, 10, 10, 2, 9, 2, 5],
    ![0, 0, 7, 0, 9, 8, 0, 9, 8, 0, 8, 9, 0, 7, 7],
    ![2, 7, 7, 6, 11, 2, 2, 6, 11, 11, 6, 2, 7, 2, 7],
    ![3, 7, 7, 5, 3, 12, 3, 12, 5, 12, 3, 5, 7, 7, 3]]

private def kindNumber : Kind → Fin 15
  | .inl b => b.castLE (by decide)
  | .inr l => l.natAdd 2

theorem points_share_line (p q : Point) :
    ∃ l : Fin 13, incident p (.inr l) ∧ incident q (.inr l) := by
  refine ⟨lineWitness p q, ?_⟩
  fin_cases p <;> fin_cases q <;> exact ⟨rfl, rfl⟩

theorem blocks_share_point (a b : Kind) :
    ∃ p : Point, incident p a ∧ incident p b := by
  refine ⟨commonPointWitness (kindNumber a) (kindNumber b), ?_⟩
  rcases a with a | a <;> rcases b with b | b <;>
    fin_cases a <;> fin_cases b <;> exact ⟨rfl, rfl⟩

private def missingBlock : Point → Kind :=
  ![.inr 0, .inl 1, .inl 1, .inl 1, .inl 1, .inl 1, .inl 1,
    .inl 0, .inl 0, .inl 0, .inl 0, .inl 0, .inl 0]

private def missingPoint : Fin 15 → Point :=
  ![7, 1, 0, 1, 0, 0, 4, 0, 0, 1, 0, 0, 1, 0, 0]

theorem point_misses_block (p : Point) : ∃ b : Kind, ¬ incident p b := by
  refine ⟨missingBlock p, ?_⟩
  fin_cases p <;> decide

theorem block_misses_point (b : Kind) : ∃ p : Point, ¬ incident p b := by
  refine ⟨missingPoint (kindNumber b), ?_⟩
  rcases b with b | b <;> fin_cases b <;> decide

theorem covered_by_special (p : Point) : incident p (.inl 0) ∨ incident p (.inl 1) := by
  fin_cases p <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem line_count (p : Point) :
    (Finset.univ.filter (fun l : Fin 13 => incident p (.inr l))).card = 4 := by
  fin_cases p <;> rfl

theorem block_size (b : Kind) : (points b).card ≤ 7 := by
  rcases b with b | b <;> fin_cases b <;> decide

end WOWII255
