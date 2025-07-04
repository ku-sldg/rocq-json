From RocqJSON Require Import JSON_Type JSON_Stringification JSON_Axioms.
From RocqCandy Require Export All.

Global Instance Stringifiable_JSON : Stringifiable JSON. 
ref (Build_Stringifiable _
  JSON_to_string
  JSON_from_string
  JSON_canonical_stringification).
Qed.