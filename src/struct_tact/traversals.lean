open tactic

def for_m {m : Type → Type} {α β : Type} [monad_m : monad m] (action : list α) (f : α → m β) : m (list β) :=
monad.mapm f action

private meta def until_first_hyp_aux (f : expr → tactic unit) : list expr → tactic unit
| [] := tactic.fail "until_first_hyp: provided tactic did not succed on any hypotheses"
| (h :: hs) := f h <|> until_first_hyp_aux hs

meta def until_first_hyp (action : expr → tactic unit) : tactic unit :=
  do ls ← local_context,
     until_first_hyp_aux action ls

def subterm_err_msg := "subterms: only provides subterms of applications; i.e terms of the form (f x_1 ... x_n) found"

meta def subterms : expr → (expr → list expr → tactic unit) → tactic unit
| (expr.app f g) action :=
  let head := expr.get_app_fn (expr.app f g),
      args := expr.get_app_args (expr.app f g)
  in action head args <|> list.foldl (<|>) (tactic.fail subterm_err_msg) (args.map (fun e, subterms e action))
| term _ := tactic.fail (subterm_err_msg ++ to_string term)

meta def tree_repeat_inner (t2 : tactic unit) : tactic unit :=
do seq t2 tree_repeat_inner, return ()

meta def fix_aux : ℕ → tactic unit → tactic unit
| last tac :=
  do n ← num_goals,
     if n = last
     then return ()
     else do all_goals tac, fix_aux n tac

meta def fix (tac : tactic unit) : tactic unit :=
fix_aux 0 tac

meta def tree_repeat (t1 : tactic unit) (t2 : tactic unit) : tactic unit :=
  do (target :: targets) ← get_goals,
     set_goals [target],
     t1,
     fix t2,
     new ← get_goals,
     set_goals (new ++ targets),
     return ()
