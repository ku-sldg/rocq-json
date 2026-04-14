From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From rocq_json_derivers Extra Dependency "namer.elpi" as namer.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi Require Import derive.
From elpi Require Import derive.std.

From Stdlib Require Import String.

Local Open Scope string_scope.

Elpi Db derive.namer.db lp:{{
  % [myder T D] links a type T to a derived concept D
  pred namer o:gref, o:gref.

  % [namer-done T] mean T was already derived
  pred namer-done o:gref.
}}.

Elpi Command derive.namer.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.namer.db.
Elpi Accumulate File namer.
Elpi Accumulate lp:{{
  main [str I] :- !, 
    coq.locate I GR,
    coq.gref->id GR Tname,
    Prefix is Tname ^ "_",
    derive.namer.main GR Prefix _.

  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.namer <object name>".
}}.

Elpi Accumulate derive Db derive.namer.db.
Elpi Accumulate derive File namer.
Elpi Accumulate derive lp:{{
  derivation GR Pref ff (derive "namer" (derive.namer.main GR Pref) (namer-done GR)).
}}.

Elpi derive Ascii.ascii.
Print ascii_namer.

derive string.
Print string_namer.

derive Inductive test := 
  | A (x : nat) 
  | B (s1 : string) (s2 : string) 
  | C : test -> test.
Print test_eqb_OK_sumbool.

Elpi Command jsoner.
Elpi Query lp:{{
  coq.say "Testing"
  ,coq.locate "test" (indt GR)
  ,Name is {coq.gref->id (indt GR)} ^ "_to_json"
  ,coq.say "Name is " Name

  ,T = global (indt GR)
  ,coq.env.indt GR Ind ParNo UParNo IndSort K KT
  ,std.assert! (Ind = tt) "jsoner: coinductive types are not supported"
  ,coq.say "Inductive " GR "takes " ParNo " parameters"
  ,coq.say "Inductive " GR "takes " UParNo " uniform parameters"
  ,coq.say "Inductive " GR "has sort " IndSort
  ,coq.say "Inductive " GR "has " K " constructors, with types " KT
  ,coq.locate "Stdlib.Strings.String.string" StrTy

}}.