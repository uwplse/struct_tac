
open lean
open interactive.types
open tactic

@[user_attribute] meta def auto_lemma_attr : user_attribute unit :=
{ name := `auto_lemma, descr := "Mark a lemma availble for use in the auto tactic." }

meta def auto_attr_handler (inductive_name : name) : command :=
do e ← get_env,
   when (¬e.is_inductive inductive_name)
     (fail $ "auto attribute failed, target is not an inductive datatype: " ++ to_string inductive_name),
   let ctors := e.constructors_of inductive_name,
   monad.mapm (fun ctor,
    do user_attribute.set auto_lemma_attr ctor () tt) ctors,
   return ()

@[user_attribute] meta def auto_attr : user_attribute unit :=
{ name := `auto, descr := "make constructors availble for use in auto tactic",
  after_set := some (λ n _ _, auto_attr_handler n)
}

meta def auto : tactic unit :=
do ls ← local_context,
   ns ← attribute.get_instances `auto_lemma,
   cs ← monad.mapm (fun n, mk_const n) ns,
   -- trace $ ("Lemmas: " ++ to_string ls ++ to_string cs),
   tactic.back_chaining_using (ls ++ cs) <|> tactic.fail "auto tactic failed"
