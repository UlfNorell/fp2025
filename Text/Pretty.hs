
module Text.Pretty
  ( module Text.Pretty
  , module Export
  ) where

import Text.PrettyPrint.HughesPJClass as Export hiding ((<>), first)

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

showP :: Pretty a => a -> String
showP = show . pPrint

pShow :: Show a => a -> Doc
pShow = text . show

