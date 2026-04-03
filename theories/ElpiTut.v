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