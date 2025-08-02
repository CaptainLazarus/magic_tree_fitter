open Domain_types

type sppf_node =
  { meta : token_info
  ; children : sppf_node list Option.t
  }
