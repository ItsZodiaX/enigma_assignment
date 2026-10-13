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

let step _config =
  failwith "Unimplemented"

let cipher _config _s =
  failwith "Unimplemented"

let hours_worked = 0
