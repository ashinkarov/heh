type t =
    | Internal
    | Source of {
        fname: string;
        line: int;
        col: int;
      }

type 'a loc =
    {
        value : 'a;
        loc : t;
    }

let mk fname l c = Source {fname=fname; line=l ; col=c}

let internal = Internal

let to_str = function
    | Internal ->
        Printf.sprintf "<loc internal>"
    | Source { fname=fname; line=l; col=c } ->
        Printf.sprintf "%s:%d:%d" fname l c

