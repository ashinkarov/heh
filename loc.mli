type t

type 'a loc

val mk: string -> int -> int -> t

val internal: t

val to_str: t -> string
