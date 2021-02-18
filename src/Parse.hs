module Parse where
import Relude

import Text.Megaparsec

type Parser = Parsec Void Text
