import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

namespace IncLoLang

/-! ## State-/

meta def tactic.dec_trivial := `[exact dec_trivial]

-- def state : Type := string × ℕ -> Prop

-- def state.update : string -> ℕ -> state -> state
-- | name val s := (λ pair, pair == (name, val) ∨ s pair)

-- notation s `{` name ` ↦ ` val `}` := state.update name val s

-- @[simp] lemma update_apply (name : string) (val : ℕ) (s : state) :
--   s{name ↦ val} (name, val) :=
-- begin
--   unfold state.update,
--   finish,
-- end

-- @[simp] lemma repeat (name : string) (val : ℕ) (s : state) :
--   s{name ↦ val}{name ↦ val} = s{name ↦ val} :=
-- begin
--   unfold state.update,
--   finish,
-- end

def state: Type := string -> ℕ

def state.update : string -> ℕ -> state -> state
| name val σ := (λ name', if name' = name then val else σ name')

notation s `{` name ` ↦ ` val `}` := state.update name val s

@[simp] lemma state.update_apply (name : string) (val : ℕ) (s : state) :
  s{name ↦ val} name = val :=
begin
  unfold state.update,
  finish,
end

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ) (s : state)
    (h : name' ≠ name) :
  s{name ↦ val} name' = s name' :=
begin
  unfold state.update,
  exact if_neg h,
end

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma update_swap (name₁ name₂ : string) (val₁ val₂ : ℕ) (s : state)
    (h : name₁ ≠ name₂ . tactic.dec_trivial) :
  s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma update_id (name : string) (s : state) :
  s{name ↦ s name} = s :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end

@[simp] lemma update_same_const (name : string) (val : ℕ) :
  (λ_, val){name ↦ val} = (λ_, val) :=
by apply funext; simp

/-! ## Language -/

inductive stmt : Type
| skip      : stmt
| assign    : string → (state → ℕ) → stmt
| seq       : stmt → stmt → stmt
| error     : stmt
| assumes   : (state → Prop) → stmt
| choice    : stmt → stmt → stmt
| star      : stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

postfix `**` : 90 := stmt.star

end IncLoLang