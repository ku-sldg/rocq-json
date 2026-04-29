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

let rec nat_of_int n =
  if n <= 0 then J.O else J.S (nat_of_int (n - 1))

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
  let handwritten_point = J.point2D_Jsonifiable' in
  let handwritten_role = J.userRole_Jsonifiable' in
  let handwritten_tree = J.binTree_Jsonifiable' nat_jsonifiable in
  bench "point2d_generated" (roundtrip generated_point.J.to_JSON generated_point.J.from_JSON point_values);
  bench "point2d_handwritten" (roundtrip (handwritten_point nat_jsonifiable).J.to_JSON (handwritten_point nat_jsonifiable).J.from_JSON point_values);
  bench "userrole_generated" (roundtrip generated_role.J.to_JSON generated_role.J.from_JSON role_values);
  bench "userrole_handwritten" (roundtrip (handwritten_role nat_jsonifiable string_jsonifiable).J.to_JSON (handwritten_role nat_jsonifiable string_jsonifiable).J.from_JSON role_values);
  bench "bintree_generated" (roundtrip generated_tree.J.to_JSON generated_tree.J.from_JSON tree_values);
  bench "bintree_handwritten" (roundtrip handwritten_tree.J.to_JSON handwritten_tree.J.from_JSON tree_values)
