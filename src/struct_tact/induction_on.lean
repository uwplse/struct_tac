open tactic
open interactive

meta def mk_eqs : list expr → tactic (list name)
| [] := return []
| (e :: es) :=
    match e with
    | (expr.local_const _ _ _ _) :=
        mk_eqs es
    | _ := do n ← get_unused_name `index,
              ty ← infer_type e,
              tactic.definev n ty e,
              eq_n ← get_unused_name `eq,
              nloc ← get_local n,
              eql ← to_expr ``(%%nloc = %%e),
              pr ← to_expr ``(eq.refl %%e),
              tactic.note eq_n eql pr,
              ns' ← mk_eqs es,
              get_local eq_n >>= revert,
              return (n :: ns')
    end

meta def induction_preserve_constants (induction_var : name) : tactic unit :=
    do loc ← get_local induction_var,
       ty ← infer_type loc,
       match ty with
       | (expr.app _ _ ) :=
        let fn := expr.get_app_fn ty,
            args := expr.get_app_args ty
        in do -- tactic.trace (to_string args),
              ns ← mk_eqs args,
              -- tactic.trace_state,
              iv ← get_local induction_var,
              seq (`[induction iv])
                (do monad.mapm (fun n, get_local n >>= revert) ns,
                    `[try { dsimp * }],
                     intros,
                    -- generalize me
                    -- monad.mapm (fun _, do n ← get_unused_name `eq, intro n >>= subst) ns,
                    return ())
       | _ := do iv ← get_local induction_var,
                 `[induction iv]
       end

/-- A specialized version of induction which fixes some flaws present in the default induction tactic.

    So far it supports two new features, it will introduce up to the named variable this behavior is similar
    to Coq's induction tactic, and allows you to start proofs with goals of the form:

    -------------
    |- forall (x_1 : t_1) ... (x_n : t_n), Goal

    With the invocation `induction x_i` where `x_i` is one the names mentioned in the above quantifier.

    The second feature side-steps the fact that induction "forgets" constant indicies, we first traverse
    the type of the induction target collecting non-locals, then we introduce fresh bindings for each
    constant, and equality which can be inhabited with `refl`, revert the equalities so they are in the
    goal before we invoke induction. We can then rewrite with these equalities in each sub goal to restablish
    that the indices were equal to some constant. -/
meta def induction_on (induction_var : parse lean.parser.ident) : tactic unit :=
do tgt ← target,
   match tgt with
   | (expr.pi binder_name _ _ _) :=
     if binder_name = induction_var
     then do intro binder_name,
             induction_preserve_constants binder_name,
             return ()
     else do intro binder_name, induction_on
   | _ := induction_preserve_constants induction_var
   end
