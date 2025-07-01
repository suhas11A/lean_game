-- import Game.Levels.Basics
import Game.Levels.PropositionalLogic
import Game.Levels.VariablesAndQuantifiers
import Game.Levels.Sets
import Game.Levels.SetOperations
-- import Game.Levels.Functions
import Game.Levels.WeakInd

-- Here's what we'll put on the title screen
Title "Infinite Descent in Lean"
Introduction
"
An adaptation of [Infinite Descent into Pure Mathematics](https://infinitedescent.xyz) into Lean.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use markdown.
"
-- Dependency Basics → PropositionalLogic

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
