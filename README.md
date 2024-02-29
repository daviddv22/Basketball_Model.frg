# Basketball_Model.frg
A modeling of a simplified basketball game in Forge

## Is there evidence you explored a model you are curious in?

We chose to model basketball in forge. Given that we can model many things in forge, we thought it would be interesting to model basketball. However, as we continued to model basketball, we found it difficult to model non-logical things such as health, luck, and other non-logical factors. Nonetheless, we were able to model a small subset of basketball and found that the model was interesting and reflected the real world. With the time constraints and visual capabilities, we choose to model a small subset of basketball, but we are still curious to see how we could model a full game of basketball in forge.

Being basketball fans, we are curious about the following questions:
- How can we model a basketball game in forge?
- How can we model the players in a basketball game in forge?
- How can we model the each play of a basketball game in forge?

From these question, we wanted to see if there were any patterns to the outcome of games. Additionally, we wanted to see if a basketball game solely based on logic would yield the same results as a real game. Although simplified, from the results we found the game to be logical and could reflect how a real game would be played.

In the process of modeling basketball in forge, we found that there were a lot more rules and constraints than we initially thought. This made the model more complex, but also more interesting. Although we are submitted a less complex version of the model, we were curious how we could model other things such as the fouling system. We had commented to logic that would help us model fouls, but we choose to not include it in the final model as it made the graph visual extremely complex and difficult to read. 

## Evidence you validated your model (tests, under constraints and over constraints)

In order to validate our model, we created assertion test for all of our predicates, checking the logic behind our system for determine whether a game was wellformed and ensuring that wellformed games did not have negative/invalid stats. We also made sure that a game cannot be tied and won at the same time. We also tested for whether two consecutive possessions were valid depending on the stats and made sure the scores had valid/possible numbers and that the games were also wellformed. 

To check for over constraints, we used test expects to make sure that our constraints were not too strict and made sure we are able to generate a valid system where all games are wellFormed and more specific situations like all games are wellformed and no winner in any of the games. We also tested the logic of possessions to make sure as long as any two games are a valid possession, then their scores are always valid. We also tested the opposite where as long as we can find two possessions where nextPossession is invalid, we can assume there was a oddScore in one of the two games. 

To check for under constraints, we tested for unsatisfactory conditions like paradoxes where a game could be a winner and a tie at the same time. We made sure no paradoxes happen and that our constraints are tight enough to account for these invalid conditions. We also tested to make sure that if a game is not wellformed then it cannot be instantiated as the first game, this is important to make sure the first game is valid so it doesn't mess up future games. We also made sure that there are no possessions that results in an invalid score in any of the two games involved. (prior and after). Doing these tests makes sure that our constraints are solid and not too loose. 

Overall, we make use of assertions to test our model and its predicate. However, as a further step, we could have used `test expects` to test for functionality and constraints.

From these tests, we found that our system is functional and makes sure that each game and possession are valid and that we don't run into any paradoxes or invalid stats. 

## Get something out of your curiosity model

We discovered thought we could model a lot more components that we had initially thought after breaking it down into different logical components. This was more apparent on when we attempted to model the fouling system of basketball. We found that if we were able to reason about the possible outcomes that could occur, we could model it in forge. This was interesting as it allowed us to see how we could model a complex system in forge.

We found through modeling basketball in forge that stats do play an important role in the outcome of the game. This makes sense logically, but given that a player is more likely to make a 3-point shot, even though it is more difficult to do so, they should take a 3-point shot over a 2-point shot. Additionally, we found that having a higher rebounding number is important as it allows for more chances to score.

Although these conclusion are not entirely surprising as they are things we would naturally think about in a real game, it is interesting to see that the model reflects the real world, but also implies how much outside factors such as luck, health, and other things can play a role in the outcome of a game, as our model reflects in a sense a 'perfect game'.

Furthermore, given that basketball is a large game with many constraints and players, we choose to model a small subset of plays with less players and rules. This allowed us to see how the model would work and how the outcome of the game would be, but also allows us to add more constraints in the future to better reflect the real world. Attempting to model the fouling system of basketball gave us more confidence and a better understanding of how we could model a full game of basketball in forge.

NOTE: There are some games where the Home team of the Away team have a score of zero. This follows real-life so we kept this in our model, clicking next will provide a new game with a different scores.
