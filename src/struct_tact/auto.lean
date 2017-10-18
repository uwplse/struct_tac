
open lean
open interactive.types
open tactic

-- meta def auto_attr_handler (inductive_name : name) : command :=
-- do e ← get_env,
--    when (¬e.is_inductive inductive_name)
--      (fail "constructor tactic failed, target is not an inductive datatype"),



-- @[user_attribute] meta def auto_attr : user_attribute unit :=
-- { name := `auto, descr := "make constructors availble for use in auto tactic",
--   after_set := some (λ n _ _, auto_attr_handler n)
-- }

meta def auto := tactic.back_chaining_using_hs
