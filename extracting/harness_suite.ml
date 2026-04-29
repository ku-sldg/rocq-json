module J = Jsonifiable_suite

let b v = if v then J.True else J.False

let ascii_of_char c =
  let n = Char.code c in
  J.Ascii
    ( b (n land 1 <> 0),
      b (n land 2 <> 0),
      b (n land 4 <> 0),
      b (n land 8 <> 0),
      b (n land 16 <> 0),
      b (n land 32 <> 0),
      b (n land 64 <> 0),
      b (n land 128 <> 0) )

let rec string_of_ocaml s i =
  if i = String.length s then J.EmptyString
  else J.String (ascii_of_char s.[i], string_of_ocaml s (i + 1))

let js s = string_of_ocaml s 0

let string_eq a b =
  match J.string_dec a b with
  | J.Left -> true
  | J.Right -> false

let rec nat_of_int n =
  if n <= 0 then J.O else J.S (nat_of_int (n - 1))

let rec int_of_nat = function
  | J.O -> 0
  | J.S n -> 1 + int_of_nat n

let nat_jsonifiable =
  {
    J.to_JSON = (fun n -> J.JSON_Nat n);
    from_JSON =
      (function
      | J.JSON_Nat n -> J.Res n
      | _ -> J.Err (js "expected nat"));
  }

let string_jsonifiable =
  {
    J.to_JSON = (fun s -> J.JSON_String s);
    from_JSON =
      (function
      | J.JSON_String s -> J.Res s
      | _ -> J.Err (js "expected string"));
  }

let kv k v = J.Pair (js k, v)
let nil = J.Nil
let cons x xs = J.Cons (x, xs)
let obj fields = J.JSON_Object fields

let hand_point_to_json = function
  | J.MkPoint2D (x, y) ->
      obj
        (cons
           (kv "MkPoint2D"
              (obj
                 (cons (kv "x" (J.JSON_Nat x))
                    (cons (kv "y" (J.JSON_Nat y)) nil))))
           nil)

let hand_point_from_json = function
  | J.JSON_Object
      (J.Cons
        ( J.Pair (_, J.JSON_Object (J.Cons (J.Pair (_, J.JSON_Nat x), J.Cons (J.Pair (_, J.JSON_Nat y), J.Nil)))),
          J.Nil )) ->
      J.Res (J.MkPoint2D (x, y))
  | _ -> J.Err (js "bad point")

let hand_role_to_json = function
  | J.Admin -> J.JSON_String (js "Admin")
  | J.Guest -> J.JSON_String (js "Guest")
  | J.Moderator level ->
      obj (cons (kv "Moderator" (obj (cons (kv "level" (J.JSON_Nat level)) nil))) nil)
  | J.StandardUser (id, username) ->
      obj
        (cons
           (kv "StandardUser"
              (obj
                 (cons (kv "id" (J.JSON_Nat id))
                    (cons (kv "username" (J.JSON_String username)) nil))))
           nil)

let hand_role_from_json = function
  | J.JSON_String s when string_eq s (js "Admin") -> J.Res J.Admin
  | J.JSON_String s when string_eq s (js "Guest") -> J.Res J.Guest
  | J.JSON_Object (J.Cons (J.Pair (_, J.JSON_Object (J.Cons (J.Pair (_, J.JSON_Nat n), J.Nil))), J.Nil)) ->
      J.Res (J.Moderator n)
  | J.JSON_Object
      (J.Cons
        ( J.Pair
            ( _,
              J.JSON_Object
                (J.Cons
                  ( J.Pair (_, J.JSON_Nat id),
                    J.Cons (J.Pair (_, J.JSON_String username), J.Nil) )) ),
          J.Nil )) ->
      J.Res (J.StandardUser (id, username))
  | _ -> J.Err (js "bad role")

let rec hand_tree_to_json elem_to_json = function
  | J.BinLeaf -> J.JSON_String (js "BinLeaf")
  | J.BinNode (left, value, right) ->
      obj
        (cons
           (kv "BinNode"
              (obj
                 (cons (kv "left" (hand_tree_to_json elem_to_json left))
                    (cons (kv "value" (elem_to_json value))
                       (cons (kv "right" (hand_tree_to_json elem_to_json right)) nil)))))
           nil)

let rec hand_tree_from_json elem_from_json = function
  | J.JSON_String _ -> J.Res J.BinLeaf
  | J.JSON_Object
      (J.Cons
        ( J.Pair
            ( _,
              J.JSON_Object
                (J.Cons
                  ( J.Pair (_, left_json),
                    J.Cons
                      ( J.Pair (_, value_json),
                        J.Cons (J.Pair (_, right_json), J.Nil) ) )) ),
          J.Nil )) -> (
      match
        ( hand_tree_from_json elem_from_json left_json,
          elem_from_json value_json,
          hand_tree_from_json elem_from_json right_json )
      with
      | J.Res left, J.Res value, J.Res right -> J.Res (J.BinNode (left, value, right))
      | _ -> J.Err (js "bad tree"))
  | _ -> J.Err (js "bad tree")

let point_values =
  [ J.MkPoint2D (nat_of_int 1, nat_of_int 2); J.MkPoint2D (nat_of_int 13, nat_of_int 21) ]

let role_values =
  [
    J.Admin;
    J.Moderator (nat_of_int 2);
    J.StandardUser (nat_of_int 7, js "alice");
    J.Guest;
  ]

let tree_values =
  [
    J.BinLeaf;
    J.BinNode (J.BinLeaf, nat_of_int 1, J.BinLeaf);
    J.BinNode
      ( J.BinNode (J.BinLeaf, nat_of_int 2, J.BinLeaf),
        nat_of_int 3,
        J.BinNode (J.BinLeaf, nat_of_int 4, J.BinLeaf) );
  ]

let bench name f =
  let iterations = try int_of_string (Sys.getenv "JSONIFIABLE_SUITE_ITERS") with _ -> 20_000 in
  let start = Sys.time () in
  for _ = 1 to iterations do
    f ()
  done;
  let elapsed = Sys.time () -. start in
  Printf.printf "BENCH %s %.6f\n%!" name elapsed

let roundtrip to_json from_json values () =
  List.iter
    (fun v ->
      let result = from_json (to_json v) in
      ignore (Sys.opaque_identity result))
    values

let () =
  let generated_point = J.point2D_Jsonifiable nat_jsonifiable in
  let generated_role = J.userRole_Jsonifiable nat_jsonifiable string_jsonifiable in
  let generated_tree = J.binTree_Jsonifiable nat_jsonifiable in
  bench "point2d_generated" (roundtrip generated_point.J.to_JSON generated_point.J.from_JSON point_values);
  bench "point2d_handwritten" (roundtrip hand_point_to_json hand_point_from_json point_values);
  bench "userrole_generated" (roundtrip generated_role.J.to_JSON generated_role.J.from_JSON role_values);
  bench "userrole_handwritten" (roundtrip hand_role_to_json hand_role_from_json role_values);
  bench "bintree_generated" (roundtrip generated_tree.J.to_JSON generated_tree.J.from_JSON tree_values);
  bench "bintree_handwritten"
    (roundtrip (hand_tree_to_json nat_jsonifiable.J.to_JSON) (hand_tree_from_json nat_jsonifiable.J.from_JSON) tree_values)
