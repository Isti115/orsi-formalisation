module Statement

%access public export
%default total

data Statement : Type where
  TRUE : Statement
  FALSE : Statement
  NOT : Statement -> Statement
  AND : Statement -> Statement -> Statement
  OR : Statement -> Statement -> Statement

infix 3 #!#
(#!#) : Statement -> Statement
(#!#) = NOT

infix 2 #&&#
(#&&#) : Statement -> Statement -> Statement
(#&&#) = AND

infix 1 #||#
(#||#) : Statement -> Statement -> Statement
(#||#) = OR

infix 2 #/\#
(#/\#) : Statement -> Statement -> Statement
(#/\#) = AND

infix 1 #\/#
(#\/#) : Statement -> Statement -> Statement
(#\/#) = OR

Show Statement where
  show TRUE = "TRUE"
  show FALSE = "FALSE"
  show (NOT s) = "!" ++ show s
  show (AND s1 s2) = "(" ++ show s1 ++ " /\\ " ++ show s2 ++ ")"
  show (OR s1 s2) = "(" ++ show s1 ++ " \\/ " ++ show s2 ++ ")"
