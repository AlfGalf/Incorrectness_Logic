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
| skip            : stmt
| assign          : string → (state → ℕ) → stmt
| non_det_assign  : string → stmt
| seq             : stmt → stmt → stmt
| error           : stmt
| assumes         : (state → Prop) → stmt
| choice          : stmt → stmt → stmt
| star            : stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

infixr ` <+> ` : 90 := stmt.choice

postfix `**` : 90 := stmt.star

notation `[` x ` ↣ ` e `]` := stmt.assign x e

/- This is the definition of P[x'/x] used in the paper -/
def p_thing (P: IncLoLang.state -> Prop) (x': ℕ) (x: string) : IncLoLang.state -> Prop :=
  -- λ σ', ∃ σ, P σ ∧ σ' = σ{x ↦ x'}
  -- This is the definition given int he paper but it is wrong
  λ σ', ∃ σ, P σ ∧ σ = σ'{x ↦ x'}

notation P `{` name ` ↣ ` val `}` := p_thing P val name

/-! # Language semantics -/

inductive LogicType : Type
| er
| ok

inductive lang_semantics: IncLoLang.stmt -> LogicType -> (IncLoLang.state) -> (IncLoLang.state) -> Prop
| skip {s} :
  lang_semantics IncLoLang.stmt.skip LogicType.ok s s
| seq_ok {S T s t u} (H1: lang_semantics S LogicType.ok s t) (H2: lang_semantics T LogicType.ok t u) :
  lang_semantics(S ;; T) LogicType.ok s u
| seq_er_2 {S T s t u} (H1: lang_semantics S LogicType.ok s t) (H2: lang_semantics T LogicType.er t u) : 
  lang_semantics (S ;; T) LogicType.er s u
| seq_er_1 {S T s t} (H1: lang_semantics S LogicType.er s t): 
  lang_semantics (S ;; T) LogicType.er s t
| error {s}:
  lang_semantics IncLoLang.stmt.error LogicType.er s s
| assign {x s e} :
  lang_semantics (IncLoLang.stmt.assign x e) LogicType.ok s (s{x ↦ (e s)})
| non_det_assign {x s v} :
  lang_semantics (IncLoLang.stmt.non_det_assign x) LogicType.ok s (s{x ↦ v})
| assumes_ok {s} {B: IncLoLang.state -> Prop} (h: B s) :
  lang_semantics (IncLoLang.stmt.assumes B) LogicType.ok s s
| choice_left {C₁ C₂ ty s₁ s₂} (h: (lang_semantics C₁ ty s₁ s₂)): 
  lang_semantics (IncLoLang.stmt.choice C₁ C₂) ty s₁ s₂
| choice_right {C₁ C₂ ty s₁ s₂} (h: (lang_semantics C₂ ty s₁ s₂)): 
  lang_semantics (IncLoLang.stmt.choice C₁ C₂) ty s₁ s₂
| star_base {C s ty} :
  lang_semantics (IncLoLang.stmt.star C) ty s s
| star_recurse {C s₁ s₂ ty} (h: lang_semantics (C**;;C) ty s₁ s₂):
  lang_semantics (C**) ty s₁ s₂

def free (P: state -> Prop) (x: string) : Prop := 
  ∀ v, ∀ st, (P st) ↔ (P (st{x ↦ v}))

def Free (C: state -> Prop) (x: string) : Prop :=
  ∀ σ: state, ∀ v, (C σ ↔ C (σ{x ↦ v}))

def Mod (C: stmt) (x: string) : Prop :=
  ∃ st st': state, lang_semantics C LogicType.ok st st' ∧ st x ≠ st' x

lemma mod_assign {x: string} {v: ℕ} : 
  Mod [x ↣ v] x :=
begin
  use (λ _, v+1),
  use ((λ _, v+1) {x ↦ v}),

  exact ⟨ lang_semantics.assign, by simp ⟩,
end

-- inductive Mod: stmt → string → Prop
-- | seq_left {C₁ C₂ x} (H: Mod C₁ x):
--   Mod (C₁ ;; C₂) x
-- | seq_right {C₁ C₂ x} (H: Mod C₂ x) :
--   Mod (C₁ ;; C₂) x
-- | choice_left {C₁ C₂ x} (H: Mod C₁ x) :
--   Mod (C₁ <+> C₂) x
-- | choice_right {C₁ C₂ x} (H: Mod C₂ x) :
--   Mod (C₁ <+> C₂) x
-- | star {C x} (H: Mod C x) :
--   Mod (C**) x
-- | assign {x e}:
--   Mod [x ↣ e] x
-- | non_det_assign {x}:
--   Mod (stmt.non_det_assign x) x

end IncLoLang