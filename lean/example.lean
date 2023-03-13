
import lean.language

inductive lang : Type
| skip            : lang
| assign          : string → IncLoLang.expression → lang
| non_det_assign  : string → lang
| seq             : lang → lang → lang
| if_             : IncLoLang.expression → lang → lang → lang
| loop_           : IncLoLang.expression → lang → lang
| error           : lang

def lang.to_stmt : lang → IncLoLang.stmt 
| lang.skip := IncLoLang.stmt.skip
| (lang.assign s e) := IncLoLang.stmt.assign s e
| (lang.non_det_assign s) := IncLoLang.stmt.non_det_assign s
| (lang.seq C₁ C₂) := IncLoLang.stmt.seq (C₁.to_stmt) (C₂.to_stmt)
| (lang.if_ e bt bf) := (IncLoLang.stmt.assumes (λ st, e st = 0) ;; (bt.to_stmt)) <+> (IncLoLang.stmt.assumes (λ st, e st ≠ 0) ;; (bf.to_stmt))
| (lang.loop_ e l) := (IncLoLang.stmt.assumes (λ st, e st = 0) ;; (l.to_stmt))** ;; IncLoLang.stmt.assumes (λ st, e st ≠ 0)
| lang.error := IncLoLang.stmt.error

-- instance : has_repr IncLoLang.stmt :=
--   λ x, "A"

notation a `;>` b := lang.seq a b
