open tactic

meta def trace_goals : tactic unit :=
do gs ← get_goals,
   ts ← monad.mapm infer_type gs,
   trace (to_string ts)
