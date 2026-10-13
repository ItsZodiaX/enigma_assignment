type rotor = {
  wiring : string;
  turnover : char;
}

type oriented_rotor = {
  rotor : rotor;
  top_letter : char;
}

type config = {
  refl : string;
  rotors : oriented_rotor list;
  plugboard : (char * char) list;
}

let index c = Char.code c - Char.code 'A'

let wrap n = ((n mod 26) + 26) mod 26

let map_r_to_l wiring top_letter input_pos =
  let offset = index top_letter in
  let contact = wrap (input_pos + offset) in
  let output_contact = index wiring.[contact] in
  wrap (output_contact - offset)

let letter i = Char.chr (i + Char.code 'A')

let map_l_to_r wiring top_letter input_pos =
  let offset = index top_letter in
  let contact_letter = letter (wrap (input_pos + offset)) in
  let output_contact = String.index wiring contact_letter in
  wrap (output_contact - offset)

let map_refl wiring input_pos = map_r_to_l wiring 'A' input_pos

let rec map_plug plugs c =
  match plugs with
  | [] -> c
  | (a, b) :: _ when c = a -> b
  | (a, b) :: _ when c = b -> a
  | _ :: rest -> map_plug rest c

let rec map_rotors_r_to_l rotors input_pos =
  match rotors with
  | [] -> input_pos
  | { rotor; top_letter } :: rest ->
      map_rotors_r_to_l rest input_pos |> map_r_to_l rotor.wiring top_letter

let rec map_rotors_l_to_r rotors input_pos =
  match rotors with
  | [] -> input_pos
  | { rotor; top_letter } :: rest ->
      map_l_to_r rotor.wiring top_letter input_pos |> map_rotors_l_to_r rest

let cipher_char config c =
  c
  |> map_plug config.plugboard
  |> index
  |> map_rotors_r_to_l config.rotors
  |> map_refl config.refl
  |> map_rotors_l_to_r config.rotors
  |> letter
  |> map_plug config.plugboard

let advance r = { r with top_letter = letter (wrap (index r.top_letter + 1)) }

let at_turnover r = r.top_letter = r.rotor.turnover

(** 
    - Rule 1: the rightmost rotor always steps.
    - Rule 2: a rotor other than the leftmost that is at its turnover
      steps, and so does the rotor immediately to its left.
    - Rule 3: whether each rotor steps is decided once, from the top
      letters before stepping, so no rotor steps more than once. *)
let rec step_rotors is_leftmost rotors =
  match rotors with
  | [] -> []
  | [ rightmost ] -> [ advance rightmost ]
  | r :: (right :: _ as rest) ->
      let pushed_by_right = at_turnover right in
      let pushed_by_self = (not is_leftmost) && at_turnover r in
      let r' = if pushed_by_right || pushed_by_self then advance r else r in
      r' :: step_rotors false rest

let step config = { config with rotors = step_rotors true config.rotors }

let rec cipher_chars config chars =
  match chars with
  | [] -> []
  | c :: rest ->
      let config = step config in
      cipher_char config c :: cipher_chars config rest

let cipher config s =
  s |> String.to_seq |> List.of_seq |> cipher_chars config |> List.to_seq
  |> String.of_seq

let hours_worked = 7
