globals [
  csv
  fileList ; ???? TODO: what is this?
  continue ; if the game is goal is achieved, then continue if false
  width
  height
  color-list; color for different agents
  goal ;the goal pattern
  num-hours ; the length of solution
  day ; the day
  hour; the hour

  bidding ; for each action, we record a value
  ;=========================buttons related variables==============================================
  ; noise ; the randomly set points in each button that belongs to solution.
  ; noise-dis; the randomly set points in each button that not belongs to solution.
  buttons; a list of buttons, each button is a pair setting some patches to green and some to black
  button-chosen; the (index of the) button choosen to be pressed in current hour. For day 0, hour 0, it is randomly choosen
  buttons-chosen-before; all the buttons chosen before
  ]
turtles-own[own-color; color set to the agent
  buttons-assigned; the order of buttons it owns, relating to the matrix buttons
  observation ; the agent's observation
  ;======================beliefs===================================================================
  action-knowledge; Beliefs about the actions. each action is a pair: (know-true, know-false). know-true consists of the propositions the agent is sure about.
  ; know false consists of the propositions the agent knows false about.
  best-node ; a variable to help out the depth first search
  know-buttons-in-charge; the percentage of the knownledge each agent acuired for the button(s) it in charge of.
]


; =================================================================
; ========================== The Setup part =======================
; =================================================================

to setup
  clear-all
  ;set noise 12; the randomly set points in each button that belongs to solution.
  ; set noise-dis 8; the randomly set points in each button that not belongs to solution.
  set color-list n-of num-agents [yellow magenta blue red pink brown grey];just for the sake of telling each agent apart

  reset-ticks
  open-file; set up the goal pattern.
  setup-time
  setup-button
  setup-agents
  assign-buttons
  show-vision;show the agents' vision by * mark.
  setup-bidding
  setup-patches

end


to setup-time
  set day 0
  set hour 0
end

to setup-bidding
  set bidding []
  foreach buttons[
    set bidding (fput 0 bidding)
    ]

end

; to load the goal pattern

to open-file

  file-open pattern-name
  set goal list [] []
  let delim ","

  set csv file-read-line
  let tmp split csv delim

  set width read-from-string item 0 tmp
  set height read-from-string item 1 tmp
  resize-world 0 (width - 1) 0 ( height - 1)
  set-patch-size 500 / width

  let x 0
  let y height - 1

  while [not file-at-end?]
  [
    set csv file-read-line
    set tmp split csv delim
    foreach tmp
    [
      let positive first goal
      let negative last goal

      ifelse (? = "1")
      [
        ; ask patch x y [set pcolor green]
        ; positive
        set goal (list (fput (x + y * width) positive) negative)
        set x x + 1
        if (x = width)
        [
          set x 0
          set y y - 1
        ]
      ]
      [
        ; negative
        set goal (list positive (fput (x + (y) * width) negative))
        set x x + 1
        if (x = width)
        [
          set x 0
          set y y - 1
        ]
      ]
    ]
  ]

  file-close
end

to-report split [ string delim ]
  report reduce [
    ifelse-value (?2 = delim)
      [ lput "" ?1 ]
      [ lput word last ?1 ?2 but-last ?1 ]
  ] fput [""] n-values (length string) [ substring string ? (? + 1) ]
end

; to load and display the goal
to load-and-display-goal
  clear-all
  open-file
  foreach (first goal) [
    let x ? mod width
    let y floor (? / width)
    ask patch x y [set pcolor green]
    ]
end

;==============the initial states=============================================================================
;it is assumed that the initial state is black, i.e. all lights off.


to setup-patches
  ask patches[set pcolor black ]
end


to setup-button

  set buttons-chosen-before []
  ; the total number of buttons =  num-agent * buttons-each
  ; we choose the first half and one more of the buttons as the plan

  let solution-buttons [] ; the solution plan to be achieved

  ;change the goal representation so patches to be set to black are represented as a negative number
  let goal-combination first goal
  foreach (last goal) [set goal-combination lput ( -1 * ? ) goal-combination]
  let total-buttons buttons-each * num-agents
  set num-hours ( floor ( total-buttons / 2 ) + 1 ) ; the total number of steps for this plan, which is 1 + half of the total number of buttons

  ;----------------------------------------------------------
  ; Part one: buttons leading to solution

  let choose-num floor (( length goal-combination ) / ( num-hours - 1 )) ; the least number of propositions in each button

  ; here we use floor to avoid running out of propositions before the tidy up step (the last step)
  foreach n-values ( num-hours - 1 ) [?] ;each button that leads to solution without the step to tidy up the randomness

  [
   let remain-g-c goal-combination
   let chosen n-of choose-num remain-g-c
   set remain-g-c (remove chosen remain-g-c ) ; the remaining ones to be satisfied/choosen in further steps

   let pos []
   let neg []
   foreach chosen [
     ifelse (? >= 0)[
       set pos (lput ? pos)
     ][
     set neg ( lput (-1 * ?) neg )]
   ] ; initialise the pair of pos and neg


  ;-----------------------------------------
  ; buttons with random values towards the goal
   let noise-vals n-of noise (n-values (length goal-combination) [?]);randomly choose positions in the goal with the number of noise
   ; check if the random positions is already in the buttons, if not add it to the button.
   foreach noise-vals [
     ifelse ((member? ? pos) or (member? ? neg) )[

       ][
       ifelse (random 2 > 0)[
         set pos fput ? pos
         ][
         set neg fput ? neg
         ]
       ]
     ]
   set solution-buttons fput (list pos neg) solution-buttons
   ]



  foreach solution-buttons [ perform-action  ? ]
 ; a tidy up button
  let last-pos []
  let last-neg []
   ask patches [
    let index (width * pycor + pxcor)
    if ((pcolor = black) and (member? index (first goal)))[set last-pos (lput index (last-pos))] ; should be green and is green now
    if ((pcolor = green) and (member? index (last goal)))[set last-neg (lput index (last-neg))]; should be black but is green now
    ]

   let last-btn (list last-pos last-neg)
   set solution-buttons lput (last-btn) solution-buttons


   perform-action last-btn

  ;----------------------------------------------------------
  ; Part 2: buttons not leading to patterns,i.e. disturbing the agents.

   let disturbing-buttons []
   let noise-dis  (choose-num + noise) ; the number of propositions in the disturbing buttons
    foreach n-values  ( buttons-each * num-agents - num-hours ) [?][
      let noise-dis-vals []
      ifelse (noise-dis <= length goal-combination)[
        set noise-dis-vals n-of noise-dis (n-values (length goal-combination) [?]);randomly choose the elements
        ][
        set noise-dis-vals n-of (length goal-combination) (n-values (length goal-combination) [?]);randomly choose the elements
        ]

    let pos-d  []
    let neg-d  []
    foreach noise-dis-vals [
    ifelse (random 2 > 0)[set pos-d fput ? pos-d]
    [set neg-d fput ? neg-d];randomly set the sign (on/off) to the elements
    ]

   set disturbing-buttons fput (list pos-d neg-d ) disturbing-buttons

    ]

   set buttons sentence solution-buttons disturbing-buttons ; append the disturbing buttons to the solution buttons

end


to setup-agents
  let all-black [];get the index of all the patches
  ask patches [set all-black (fput (get-patch-index self) all-black)]

  create-turtles num-agents [
    set know-buttons-in-charge 0
    set label who
    setxy random-xcor random-ycor
     face patch-here
      move-to patch-here
    ; set the observation to black everywhere

    ;initialize the knowledge of actions,
    set action-knowledge []
    let k-tmp (list [] [])
    foreach n-values (length buttons)[?] [
      set action-knowledge (fput k-tmp action-knowledge)
      ]
    ; the agent's initial observation is simply all black

    set observation all-black

    ]
    foreach (n-values num-agents [?]) [ ask turtle ? [ set color item ? color-list] ];set different colors to agents.

end




to show-vision
  ask patches [set plabel ""]
  ;visulize of the vision,setting plabels in the vision
   ask turtles [
    set own-color color
    let oc own-color

       ask patches in-cone-nowrap vision-radius 360
          [
;            set pcolor pcolor + 1; this code trace the routes(and vision) the agents go, you can delete it if you don't like it.
           set plabel-color oc
           set plabel "*"    ]
      ]
end

to-report get-patch-index [p]
  ifelse ([pcolor] of p = green) [report ([pycor] of p * width + [pxcor] of p)]
  [report ([pycor] of p * width + [pxcor] of p) * -1]
end

; =================================================================
; ========================== The Go part ==========================
; =================================================================

to go
;  ask patches [set pcolor black]
  ; for day 0, hour 0 the button of the hour is randomly choosen.
  ifelse (hour < num-hours)
  ; ====================== in day time =================================
  [
    show "in day time"
    ; first of all choose the action to perform for this hour.
    ifelse (day = 0 and hour = 0)
    [
      set button-chosen one-of (n-values length buttons [?])
      set buttons-chosen-before (fput button-chosen [])

      ] ;  select a random action and record its index and there is no button chosen before
    [


      ifelse (total-knowledge > knowledge-threshold * 0.01 )
      [bid]
      [set bidding (n-values (length buttons) [0])]; if we have not reached the knowledge threshold, then we randomly select

      let max-value (max bidding)
      ; then obtain the indexes with this value (those got chosen before remains zero)
      set button-chosen (one-of (filter [((item ? bidding)= max-value) and not (member? ? buttons-chosen-before)] n-values (length buttons)[?])); choose one of those with the best bidding value
      set buttons-chosen-before (fput button-chosen buttons-chosen-before)
      ; choose the button with the highest bidding value
    ]
    ; then perform the action
    perform-action item button-chosen buttons
    show button-chosen
    show check-goal
    if (check-goal) [
      show "Game Over"
      show "The total days taken is: "
      show day
      stop
      ask turtles [stop]
      ]
    ; then the agent observe and perform learning
    observe-and-learn
    ; the agent start the bidding of the next action (with values stored in the "bidding")

    ; next hour
    walk
    show-vision
    update-average-individual-knowledge
    set hour (hour + 1)
  ]
  [ ; ====================== at night =================================
    set buttons-chosen-before []
    show "at night"
    ask patches [set pcolor black]
    set hour 0
    set day (day + 1)
    ; communicate
    ; TODO: decide the first button to be pressed and the location in the morning

    walk
    show-vision
    ]

  ; if the hour = num-hours then it's another day
  show-vision
  tick
end

to-report total-knowledge
  let pct 0
  ask turtles [
    set pct (pct + know-buttons-in-charge)
    ]
  set pct (pct / num-agents)
  report pct
end


to update-average-individual-knowledge; the average knownledge of the buttons each agent in charge of.
  ask turtles[
    ;let total-indi-know 0; the knowldege of all the buttons it
    set know-buttons-in-charge 0
    foreach buttons-assigned[
     let n length first (item ? action-knowledge)
      set know-buttons-in-charge ( know-buttons-in-charge + n / (width * height))
    ]
    set know-buttons-in-charge (know-buttons-in-charge / buttons-each)
  ]

end

to-report check-goal ; check if the current situation is the same as the goal
  let sign true
  foreach (first goal)[
    let x getx ?
    let y gety ?
    if (not (([pcolor] of (patch x y)) = green))[set sign false]
    ]
  foreach (last goal)[
    let x getx ?
    let y gety ?
    if (([pcolor] of (patch x y)) = green)[set sign false]
    ]
  report sign
end

; two helping function to get the xcor and ycor of the patch according to its index
to-report getx [n]
   report (n mod width)
end

to-report gety [n]
  report (floor (n / width))
end


to observe-and-learn ; ask each agent to change the vision and vision index
  ask turtles [
    let vision (patches in-cone-nowrap vision-radius 360) ; the agent's vision
    let vision-indexes []
    ask vision [
      set vision-indexes fput (get-patch-index self)  vision-indexes
      ]

    ; compare vision-indexes and observation to learn

    ; Step 1: obtain those not changed
    let know-false last (item button-chosen action-knowledge)
    let know-true first (item button-chosen action-knowledge)

    let not-changed (modes (sentence observation vision-indexes))

    let new-know-false []
    foreach not-changed [
      ifelse (? > 0)
      [set new-know-false fput (? * 3 + 1) new-know-false]
      [set new-know-false fput (? * -3 + 0) new-know-false]]; compute the new knowledge obtained from vision and observation
    set know-false remove-duplicates (sentence know-false new-know-false) ; extract information and add to belief of this action remove-duplicates
    ; Step 2: obtain those changed

    let tmp (sentence (map [? * -1] observation) vision-indexes)
    let changed []
    if (not (modes tmp = tmp)) [set changed modes tmp] ; be careful about this line. if there is no repeated element then it would simply return the original list back!!!

    let new-know-true []
    foreach changed [
      ifelse (? > 0)
      [set new-know-true fput (? * 3 + 0) new-know-true]
      [set new-know-true fput (? * -3 + 1) new-know-true]]; compute the new knowledge obtained from vision and observation

    set know-true (remove-duplicates (sentence know-true new-know-true))


    ; Before we changed the knowledge about the action, we need to make sure that there

    ; if we know that the action does not have any effect in both cases when a certain patch is on or off. Then we have say it has no effect
    foreach (n-values (width * height) [?])[
      ; if ? * 3 and ? * 3 +1 are both members of know-false then we add ? * 3 + 2 to know true. That is, we know the effect of this action on this patch.
      if((member? (? * 3) know-false) and (member? (? * 3 + 1) know-false) and not (member? (? * 3 + 2) know-true))[
        set know-true (fput (? * 3 + 2) know-true)
        set know-false (remove (? * 3 + 1) know-false)
        set know-false (remove (? * 3 ) know-false)
        ;show know-true
        ]
      ]


    ; replace the knowledge of the action
    set action-knowledge replace-item button-chosen action-knowledge (list know-true know-false)

    ; and finally, set vision-indexes as the new observation
    set observation vision-indexes; TODO: what if after walk, there is no information about new local pathes?
    ]

end



to communicate
   ; to combine all the action-button of every agent, getting a learning result:action-communication.
   let integration []

   foreach n-values (length buttons) [?][
   ; for each agent, we take the all their knowledge
   let know-true []
   let know-false []
   ask turtles [
     set know-true (remove-duplicates sentence know-true first (item ? action-knowledge))
     set know-false (remove-duplicates sentence know-false last (item ? action-knowledge))
     ]
   ; TODO: extract information from know-false to know-true

   set integration (lput (list know-true know-false) integration)
   ]

   ask turtles [
     set action-knowledge integration
     ]
end




;==============variable related to the setup of buttons=============================================================================
;goal: a list with two lists, the first list indicates the "on" positions, the second indicates "off" positions.
;solution-length:the number of buttons that leads to the pattern. The last one button cleans the random sets in the previous buttons.
;noise: number of random elements in each solution button.
;noise-vals:a list consisting of the randomly chosen position in the goal-combination list, with the length eq to noise.
;choose-num: the extent to which a button's result is similar to the goal.An absolte value.
;chosen: a list consisting of the elements in the goal-combination that is chosen to a solution button.
;buttons: the matrix consisting of lists, each of which is one button that leads to the pattern.
;disturbing-buttons: the matrix consisting of lists, each of which is one button that leads to anything but the pattern.
;buttons: the matrix consisting of lists, each of which is one button, with the buttons leading to the solution coming first.
;noise-dis: number of random elements in each disturbing button.
;noise-dis-vals: list consisting of lights (position) related to the environment.But they have notthing to do with the goal.
;==============the design of the buttons========================================================================
;Every agent has the same number of buttons, so the total number of buttons in the model is decided by the multiplication of (buttons-each * num-agents).
;We set first half of the total buttons to be the solution, i.e. a list of buttons leading to the goal. ( if the total number of the buttons is odd, we set first ( half + 0.5 ) buttons to be the solution.
;All the solutions buttons form the matrix called "buttons", the remaining buttons form the matrix called "disturbing-buttons".
;Each solutions buttons in the matrix "buttons" except the last one , gets equal amount part of similarity to the goal pattern, but different elements of the goal pattern.
;The last button in the solution matrix is set to tidy up all the indifference to the goal pattern, by performing/pressing the pervious buttons in sequene and compared the outcome with the goal pattern.
;All of the buttons in the matrix is nothing more than randomly set buttons.
;All the buttons form the matrix called "buttons", in which the solution buttons come before the remaining buttons. And the sequence in this matrxi determines the serial number for the button.



;==============the assignment of buttons to turtles============================================================
;Randomly assigned. The serial number for the button is the sequence of the buttons in the matrix "button-all", it is always that the first half or first (half + 0.5) buttons is the solution buttons.
;


to assign-buttons; randomly assign the buttons to the turtles
   let remain-bt buttons; variables remained when assigning buttons to agents one by one
   ask turtles[
   set buttons-assigned []
    foreach n-values buttons-each [?][
    let n-button ( random  (length remain-bt ))
    set buttons-assigned lput ((position  (item n-button remain-bt) buttons ) ) buttons-assigned
    set remain-bt (remove (item n-button remain-bt) remain-bt )

   ]
  ]
end




to perform-action [act]

  let pos first act
  let neg last act
  foreach pos [
    let y floor( ? / width )
    let x ( ? - y * width )
    ask patch x y [set pcolor green]
    ]

    foreach neg [
    let y floor( ? / width )
    let x ( ? - y * width )
    ask patch x y [set pcolor black]
    ]
end

;==================================bidding and planning===========================================
; datatype for depth-first searching as planning
; a tuple of the followings:

; the bidding value
; the plan so far
; the world

to bid ; calculate the bidding value for each agent for each action
  ;a new bidding round
  reset-bidding

  ; ********* a simple planning algorithm *********
  ; simple-bidding

  ; ********* depth-first searching as planning *********

  ; initialise the planning part
  ; 1) construct an instance of the date structure
  ask turtles [
  let world-now represent-visable-world
  let current-node obtain-node (calculate-bidding world-now) buttons-chosen-before world-now
  depth-first-planning current-node
  ; 2) extract information from the best-node
  if (not (best-node = [])) [
    let act-best item (length buttons-chosen-before) (reverse item 1 best-node)
    if (item act-best bidding < (item 0 best-node)) [set bidding replace-item act-best bidding (item 0 best-node)]; then update the bidding
    ]
  ; change the bidding
  ]
end

; the result is a pair of action and the bidding value
to depth-first-planning [current-node]
  ; first, obtain the node with the best bidding value
  let stack (fput current-node [])
  set best-node []
  depth-first-planning-rec stack
end

to depth-first-planning-rec [stack]
  ifelse(not (stack = []))[
    let node (first stack)

    let bv item 0 node
    let pl item 1 node ; the list of actions performed so far
    let wd item 2 node

    ; find all the actions performable in this world (i.e. not in the plan)
    ; the variable acts is the remaining buttons to be chosen for this hour
    let acts (n-values length buttons [?])
    foreach pl [
      set acts (remove ? acts);
      ]
   show "**** expand the following branches *****"
   print "  world"
   print wd
   print "  acts"
   print acts
   print "  plan so far"
   print pl
   show "****************************************"


;    ifelse (not (length acts = 0)) [
   ifelse (length pl < num-hours) [
      foreach acts [
        let pl' (fput ? pl)
        let wd' (expected-world wd (item ? action-knowledge))
        let bv' calculate-bidding wd'
        let node' obtain-node bv' pl' wd'

          ifelse ( length pl' = num-hours)
          [
            ifelse (best-node = [])
            [set best-node node']
            [if ( bv' > (item 0 best-node))[set best-node node']] ; if it is better than the best node
          ][
            if (not(wd' = []))[ ; avoid nodes where there is no knowledge
              ; add to the stack

              show "---- action and the node afterwards ------"
              show "before world:"
              show wd
              show (item ? action-knowledge)
              show "after world:"
              show wd'
              show "----- plan and bidding value -------"
              show "plan"
              show pl'
              show "bidding value"
              show bv'
              set stack (fput node' stack); add the child
              depth-first-planning-rec stack
              ]

          ]
      ]
      set stack remove node stack

    ]
    [
      set stack remove node stack
      ]

  ][
;  show "**********************end of search********************"
  ]; else if the stack is empty then do nothing



end


to-report obtain-node [v p w]
  ; TODO: this method can be simplied using task
  let node (fput w [])
  set node (fput p node)
  set node (fput v node)
  report node
end


to reset-bidding
  set bidding []
  foreach buttons [
    set bidding (fput 0 bidding)
    ]
end



; calculate the bidding function without learning factor
to-report calculate-bidding [world-after] ;  compare it with the goal and calculate a value for bidding
  let goal-on first goal
  let goal-off last goal
  let bidding-value 0
  foreach world-after[
     if (member? ? goal-on) [set bidding-value (bidding-value + 1)]
     if (member? ? goal-off) [set bidding-value (bidding-value - 1)]
     if (member? (? * -1) goal-off) [set bidding-value (bidding-value + 1)]
     if (member? (? * -1) goal-on) [set bidding-value (bidding-value - 1)]
    ]
  ; TODO: add the learning values on

  report bidding-value
end

to-report represent-visable-world ; to give the index of visable patches (for performing action in mind later)
  let rep []
  ; first obtain the list of visable patches
  let vision (patches in-cone-nowrap vision-radius 360)
  ask vision[
    ifelse (not (pcolor = green))
    [set rep (fput ((pycor * width + pxcor ) * -1) rep)]; if it is black
    [set rep (fput (pycor * width + pxcor) rep)]; otherwise it is green, positive number
  ]

  ; obtain vision index
  report rep
end

; expand according to a given action
to-report expected-world [world act]; to perform an action according to the agent's knowledge
  ;show "the knowledge of the action is as follows"
  ;show act
  ; extract the certain effect of this action
  ; first the know-true part

  let expected []

  let know-true first act;
  let know-false last act;

  foreach world [
    ; ==== the certain part of the expected world
    ; first, there is no effect,
    if ((member? (3 * ? + 2) know-true) or (member? (-3 * ? + 2) know-true))
    [
      set expected (fput ? expected)] ; if the agent knows that the action has no effect on this patch then it keeps it in the expected world
    ]

     ; the agent also knows what is going to be true and false according to its knowledge of the action
    foreach know-true [
      ; get the index
      let index floor (? / 3)
      ; get the color
      if ((remainder ? 3) = 0) [set expected (fput index expected)]
      if ((remainder ? 3) = 1) [set expected (fput (index * -1) expected)]
      ; if it is green then keep it positive, it black then keep it negative
      ]
    ; the rest is not sure for the agent.
  set expected (remove-duplicates expected)

  report expected
end


to walk
  ;ask turtles [ifelse (can-move? 1) [fd 1][right 90]]
  ask turtles[

  ifelse (hour = 0)
  ;at night
  [if(day != 0)
    [setxy random-xcor random-ycor
        face patch-here
        move-to patch-here];move to the center of the current patch, our agents will always move to the center of a patch.
        move-to-least-unknown; moves to the neighbor or current patch which has the most potential information to aquire.
      ]
  ;in the daytime
  [move-to-least-unknown]


]
end

to move-to-least-unknown; moves to the neighbor or current patch which has the most potential information to aquire.
  ;===================local variables===================================================
  ;vision-index:(if the agent was )at each neighbor patch, the invisionindex of the agent
  ;vision-known-index:(if the agent was )at each neighbor patch, the invisionindex of the agent, which the effect of current assigned button on that patch is known to current agent.

  let neighbor sort neighbors
  foreach (sentence neighbor patch-here)[;neighbor patches(at most 8 for non-boundary patches) and current patch

    let vision-index []
    let world (patches in-cone-nowrap width 360)
    ask world [if ((distancexy [pxcor] of ? [pycor] of ?) <= vision-radius)[set vision-index lput  ( pxcor + pycor * width ) vision-index]];if the agent is at this patch, its vision.
    let amount [];the amount of information it at most will get in the specific patch neighbor, for each button it owns

    foreach buttons-assigned[
      let world-known map [floor( ? / 3 )] (item 0 ( item ?  action-knowledge ))
      let vision-known-index []
      if (not (modes (sentence world-known vision-index) = (sentence world-known vision-index)))
      [set vision-known-index ( modes (sentence world-known vision-index) )]; the visionindex that already in agent's knowledge.

     set amount (lput ((length vision-index) - (length vision-known-index)) amount )
     ];the amount of information a agent at most could aquire for this button at this patch.


   ask ? [set potential-infor mean amount]; calculate the mean value(potential information) of all the buttons it is incharge of for each neighbor and current location.


    ]

    uphill potential-infor; moves to the neighbor or current patch which has the most potential information to aquire.If there are equal amount of potential infor, it randomly chooses one.

end

patches-own[potential-infor;if the agent is at that patch, with its set vision, the amount of information it at most may get.
  ]


; TODO: button generation can be done using "shuffle"
; TODO: random buttons are simply too random and looks ugly
; TODO: ask the agent to press the button, not the observer
; change all the "knowledge" to belief
@#$#@#$#@
GRAPHICS-WINDOW
841
37
1388
604
-1
-1
125.0
1
30
1
1
1
0
0
0
1
0
3
0
3
1
1
1
ticks
30.0

SLIDER
167
126
300
159
buttons-each
buttons-each
1
10
3
1
1
NIL
HORIZONTAL

BUTTON
23
439
138
472
NIL
go
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
145
438
264
471
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
24
276
162
343
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
18
126
160
159
num-agents
num-agents
2
7
2
1
1
NIL
HORIZONTAL

SLIDER
19
168
156
201
vision-radius
vision-radius
0
10
6
1
1
NIL
HORIZONTAL

MONITOR
282
518
365
563
Day
day
17
1
11

BUTTON
169
275
274
308
button 1
perform-action item 0 buttons
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
279
274
384
307
button 2
perform-action item 1 buttons
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
169
312
274
345
button 3
perform-action item 2 buttons
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
279
312
384
345
button 4
perform-action item 3 buttons
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
24
357
146
402
buttons of Agent 0
[buttons-assigned] of turtle 0
17
1
11

MONITOR
150
357
275
402
buttons of Agent 1
[buttons-assigned] of turtle 1
17
1
11

MONITOR
280
358
409
403
buttons of Agent 2
[buttons-assigned] of turtle 2
17
1
11

BUTTON
149
38
299
86
load and display
load-and-display-goal
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
164
166
302
199
noise
noise
0
13
3
1
1
NIL
HORIZONTAL

BUTTON
304
37
429
89
clear display
ask patches [set pcolor black]
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
313
126
419
172
Total buttons
num-agents * buttons-each
17
1
11

MONITOR
281
569
369
614
hour
hour
17
1
11

MONITOR
26
569
262
615
plan so far
reverse buttons-chosen-before
17
1
11

PLOT
438
58
838
610
Agents' knowledge about their buttons
total hour
knowledge (percentage)
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"Agent 0" 1.0 0 -11085214 true "" "ifelse (not (count turtles = 0)) [plot [know-buttons-in-charge * 100] of turtle 0\nset-plot-pen-color ([color] of turtle 0)] [plot 0]"
"Agent 1" 1.0 0 -13791810 true "" "ifelse (not (count turtles = 0)) [plot [know-buttons-in-charge * 100] of turtle 1\nset-plot-pen-color ([color] of turtle 1)\n] [plot 0]"
"Average" 1.0 2 -16644859 true "" "plot (total-knowledge * 100)"

SLIDER
20
203
300
236
knowledge-threshold
knowledge-threshold
0
60
0
1
1
%
HORIZONTAL

MONITOR
27
519
263
565
bidding
bidding
17
1
11

MONITOR
312
177
417
222
hours per day
num-hours
17
1
11

TEXTBOX
24
12
370
42
Step 1: Load a file (test.txt for example)
12
0.0
1

TEXTBOX
24
106
347
136
Step 2: initialise the parameters
12
0.0
1

TEXTBOX
29
252
399
270
Step 3: setup the game and initialise the buttons
12
0.0
1

TEXTBOX
30
414
180
432
Step 4: start the game!
12
0.0
1

TEXTBOX
287
493
437
511
calendar
12
0.0
1

TEXTBOX
80
494
230
512
bidding and planning
12
0.0
1

CHOOSER
22
38
145
84
pattern-name
pattern-name
"test.txt" "smile.txt"
0

TEXTBOX
447
32
614
52
Step 5: evaluation
12
0.0
1

@#$#@#$#@
## WHAT IS IT?

(a general understanding of what the model is trying to show or explain)

## HOW IT WORKS

(what rules the agents use to create the overall behavior of the model)

## HOW TO USE IT

(how to use the model, including a description of each of the items in the Interface tab)

## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

(suggested things to add or change in the Code tab to make the model more complicated, detailed, accurate, etc.)

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)

## RELATED MODELS

(models in the NetLogo Models Library and elsewhere which are of related interest)

## CREDITS AND REFERENCES

(a reference to the model's URL on the web if it has one, as well as any other necessary credits, citations, and links)
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

ufo top
false
0
Circle -1 true false 15 15 270
Circle -16777216 false false 15 15 270
Circle -7500403 true true 75 75 150
Circle -16777216 false false 75 75 150
Circle -7500403 true true 60 60 30
Circle -7500403 true true 135 30 30
Circle -7500403 true true 210 60 30
Circle -7500403 true true 240 135 30
Circle -7500403 true true 210 210 30
Circle -7500403 true true 135 240 30
Circle -7500403 true true 60 210 30
Circle -7500403 true true 30 135 30
Circle -16777216 false false 30 135 30
Circle -16777216 false false 60 210 30
Circle -16777216 false false 135 240 30
Circle -16777216 false false 210 210 30
Circle -16777216 false false 240 135 30
Circle -16777216 false false 210 60 30
Circle -16777216 false false 135 30 30
Circle -16777216 false false 60 60 30

vacuum-cleaner
true
0
Polygon -2674135 true false 75 90 105 150 165 150 135 135 105 135 90 90 75 90
Circle -2674135 true false 105 135 30
Rectangle -2674135 true false 75 105 90 120

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270

@#$#@#$#@
NetLogo 5.3
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180

shape-sensor
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0

@#$#@#$#@
0
@#$#@#$#@
