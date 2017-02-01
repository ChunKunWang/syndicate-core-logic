Axiom String : Set.
Axiom str_null : String.
Axiom str_body : String.
Axiom str_tmp_envelope : String.
Axiom str_con_data : String.
Axiom is_nullstr : String -> bool.
Axiom str_not_null : String.
Axiom str_not_null_not_null : is_nullstr str_not_null = false.

