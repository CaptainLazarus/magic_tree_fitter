open Domain_types

type gss_edge =
  { meta : token_info
  ; forward : (int * int) list
  ; backward : (int * int) list
  }

type sppf_node =
  { meta : token_info
  ; children : sppf_node list Option.t
  }
