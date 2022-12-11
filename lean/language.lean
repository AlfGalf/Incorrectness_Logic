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

def state : Type := string × ℕ -> Prop

def state.update : string -> ℕ -> state -> state
| name val s := (λ pair, pair == (name, val) ∨ s pair)

notation s `{` name ` ↦ ` val `}` := state.update name val s

@[simp] lemma update_apply (name : string) (val : ℕ) (s : state) :
  s{name ↦ val} (name, val) :=
begin
  unfold state.update,
  finish,
end

/-! ## Language -/

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| error    : stmt
| assumes : (state → Prop) → stmt
| choice : stmt → stmt → stmt
| star : stmt → stmt
-- | ite    : (state → Prop) → stmt → stmt → stmt
-- | while  : (state → Prop) → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

postfix `**` : 90 := stmt.star

end IncLoLang