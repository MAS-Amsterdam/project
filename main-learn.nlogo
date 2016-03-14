globals [
  csv
  fileList ; ???? TODO: what is this?
  continue ; if the game is goal is achieved, then continue if false
  width
  height
  color_list; color for different agents
  goal ;the goal pattern

  day ; the day
  hour; the hour

  bidding ; for each action, we record a value
  ;=========================buttons related variables==============================================
  ; noise ; the randomly set points in each button that belongs to solution.
  ; noise_dis; the randomly set points in each button that not belongs to solution.
  buttons; a list of buttons, each button is a pair setting some patches to green and some to black
  button_chosen; the (index of the) button choosen to be pressed in current hour. For day 0, hour 0, it is randomly choosen
  buttons_chosen_before; all the buttons chosen before
  ]
turtles-own[own_color; color set to the agent
  buttons_assigned; the order of buttons it owns, relating to the matrix buttons
  observation ; the agent's observation
  ;======================beliefs===================================================================
  action_knowledge; Beliefs about the actions. each action is a pair: (know_true, know_false). know_true consists of the propositions the agent is sure about.
  ; know false consists of the propositions the agent knows false about.
]


; =================================================================
; ========================== The Setup part =======================
; =================================================================

to setup
  clear-all
  ;set noise 12; the randomly set points in each button that belongs to solution.
  ; set noise_dis 8; the randomly set points in each button that not belongs to solution.
  set color_list n-of num_agents [yellow magenta blue red pink brown grey red pink blue];just for the sake of telling each agent apart

  reset-ticks
  open_file; set up the goal pattern.
  setup-time

  setup-button
  setup-bidding
  setup-patches
  setup-agents
  assign-buttons
  show-vision;show the agents' vision by * mark.

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

to open_file

  file-open pattern_name
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
  open_file
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

  set buttons_chosen_before []
  ; the total number of buttons =  num_agent * button_each
  ; we choose the first half and one more of the buttons as the plan

  let solution_buttons [] ; the solution plan to be achieved

  ;change the goal representation so patches to be set to black are represented as a negative number
  let goal_combination first goal
  foreach (last goal) [set goal_combination lput ( -1 * ? ) goal_combination]
  let total_buttons button_each * num_agents
  let solution_length ( round ( total_buttons / 2 ) + 1 ) ; the total number of steps for this plan, which is 1 + half of the total number of buttons

  ;----------------------------------------------------------
  ; Part one: buttons leading to solution

  let choose_num floor (( length goal_combination ) / ( solution_length - 1 )) ; the least number of propositions in each button

  ; here we use floor to avoid running out of propositions before the tidy up step (the last step)
  foreach n-values ( solution_length - 1 ) [?] ;each button that leads to solution without the step to tidy up the randomness

  [
   let remain_g_c goal_combination
   let chosen n-of choose_num remain_g_c
   set remain_g_c (remove chosen remain_g_c ) ; the remaining ones to be satisfied/choosen in further steps

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
   let noise_vals n-of noise (n-values (length goal_combination) [?]);randomly choose positions in the goal with the number of noise
   ; check if the random positions is already in the buttons, if not add it to the button.
   foreach noise_vals [
     ifelse ((member? ? pos) or (member? ? neg) )[

       ][
       ifelse (random 2 > 0)[
         set pos fput ? pos
         ][
         set neg fput ? neg
         ]
       ]
     ]
   set solution_buttons fput (list pos neg) solution_buttons
   ]



  foreach solution_buttons [ perform-action  ? ]
 ; a tidy up button
  let last_pos []
  let last_neg []
   ask patches [
    let index (width * pycor + pxcor)
    if ((pcolor = black) and (member? index (first goal)))[set last_pos (lput index (last_pos))] ; should be green and is green now
    if ((pcolor = green) and (member? index (last goal)))[set last_neg (lput index (last_neg))]; should be black but is green now
    ]

   let last_btn (list last_pos last_neg)
   set solution_buttons lput (last_btn) solution_buttons


   perform-action last_btn
  ;----------------------------------------------------------
  ; Part tow: buttons not leading to patterns,i.e. disturbing the agents.

   let disturbing_buttons []
   let noise_dis  (choose_num + noise) ; the number of propositions in the disturbing buttons
    foreach n-values  ( button_each * num_agents - solution_length ) [?][
    let noise_dis_vals n-of noise_dis (n-values (length goal_combination) [?]);randomly choose the elements
    let pos_d  []
    let neg_d  []
    foreach noise_dis_vals [
    ifelse (random 2 > 0)[set pos_d fput ? pos_d]
    [set neg_d fput ? neg_d];randomly set the sign (on/off) to the elements
    ]

   set disturbing_buttons fput (list pos_d neg_d ) disturbing_buttons

    ]

     set buttons sentence solution_buttons disturbing_buttons ; append the disturbing buttons to the solution buttons

end


to setup-agents
  let all_black [];get the index of all the patches
  ask patches [set all_black (fput (get-patch-index self) all_black)]

  create-turtles num_agents [
    set label who
    setxy random-xcor random-ycor
    ; set the observation to black everywhere

    ;initialize the knowledge of actions,
    set action_knowledge []
    let k_tmp (list [] [])
    foreach n-values (length buttons)[?] [
      set action_knowledge (fput k_tmp action_knowledge)
      ]
    ; the agent's initial observation is simply all black

    set observation all_black

    ]


    foreach (n-values num_agents [?]) [ ask turtle ? [ set color item ? color_list] ];set different colors to agents.
end




to show-vision
  ;visulize of the vision,setting plabels in the vision
   ask turtles [
    set own_color color
    let oc own_color
       ask patches in-cone-nowrap vision_radius 360
          [set pcolor pcolor + 1; this code trace the routes(and vision) the agents go, you can delete it if you don't like it.
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
  ask patches [set pcolor black]
  ; for day 0, hour 0 the button of the hour is randomly choosen.
  ifelse (hour <= num_hours)
  ; ====================== in day time =================================
  [
    show "in day time"
    ; first of all choose the action to perform for this hour.
    ifelse (day = 0 and hour = 0)
    [
      set button_chosen one-of (n-values length buttons [?])
      set buttons_chosen_before (fput button_chosen [])
      ] ;  select a random action and record its index and there is no button chosen before
    [
      let max_value 0
      ifelse ((length buttons) = (length buttons_chosen_before))
      [; all buttons got chosen
          set buttons_chosen_before []
          set max_value max bidding
       ][
        let bidding_no_repeat bidding
        foreach buttons_chosen_before[
           set bidding_no_repeat (replace-item ? bidding_no_repeat -999); remove the one from last time
          ]

        set max_value (max bidding_no_repeat)
        show "max"
        show max_value
      ]
      ; then obtain the indexes with this value
      set button_chosen (one-of (filter [((item ? bidding)= max_value) and not (member? ? buttons_chosen_before)] n-values (length buttons)[?])); choose one of those with the best bidding value
      set buttons_chosen_before (fput button_chosen buttons_chosen_before)
      ; choose the button with the highest bidding value
    ]
  ; then perform the action
  perform-action item button_chosen buttons
  if (check-goal = true) [
    show "Game Over"
    show "The total days taken is: "
    show day
    stop]
  ; then the agent observe and perform learning
  observe-and-learn
  ; the agent start the bidding of the next action (with values stored in the "bidding")
  bid
  ; next hour
  walk
  set hour (hour + 1)
  ]
  [ ; ====================== at night =================================
    show "at night"
    ask patches [set pcolor black]
    set hour 0
    set day (day + 1)
    communicate
    ; TODO: decide the first button to be pressed and the location in the morning
    ]

  ; if the hour = num_hours then it's another day

end

to-report check-goal ; check if the current situation is the same as the goal
  let sign true
  foreach (first goal)[
    let x getx ?
    let y gety ?
    if (([pcolor] of (patch x y)) = black)[set sign false]
    ]
  foreach (last goal)[
    let x getx ?
    let y gety ?
    if (([pcolor] of (patch x y)) = green)[set sign false]
    ]
  if sign = true [report true]
  report false
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
    let vision (patches in-cone-nowrap vision_radius 360) ; the agent's vision
    let vision_indexes []
    ask vision [
      set vision_indexes fput (get-patch-index self)  vision_indexes
      ]

    ; compare vision_indexes and observation to learn

    ; Step 1: obtain those not changed
    let know_false last (item button_chosen action_knowledge)
    let know_true first (item button_chosen action_knowledge)

    let not_changed (modes (sentence observation vision_indexes))

    let new_know_false []
    foreach not_changed [
      ifelse (? > 0)
      [set new_know_false fput (? * 3 + 1) new_know_false]
      [set new_know_false fput (? * -3 + 0) new_know_false]]; compute the new knowledge obtained from vision and observation
    set know_false remove-duplicates (sentence know_false new_know_false) ; extract information and add to belief of this action remove-duplicates
    ; Step 2: obtain those changed

    let tmp (sentence (map [? * -1] observation) vision_indexes)
    let changed []
    if (not (modes tmp = tmp)) [set changed modes tmp] ; be careful about this line. if there is no repeated element then it would simply return the original list back!!!

    let new_know_true []
    foreach changed [
      ifelse (? > 0)
      [set new_know_true fput (? * 3 + 0) new_know_true]
      [set new_know_true fput (? * -3 + 1) new_know_true]]; compute the new knowledge obtained from vision and observation

    set know_true (remove-duplicates (sentence know_true new_know_true))


    ; Before we changed the knowledge about the action, we need to make sure that there

    ; if we know that the action does not have any effect in both cases when a certain patch is on or off. Then we have say it has no effect
    foreach (n-values (width * height) [?])[
      ; if ? * 3 and ? * 3 +1 are both members of know_false then we add ? * 3 + 2 to know true. That is, we know the effect of this action on this patch.
      if((member? (? * 3) know_false) and (member? (? * 3 + 1) know_false))[
        set know_true (fput (? * 3 + 2) know_true)
        set know_false (remove (? * 3 + 1) know_false)
        set know_false (remove (? * 3 ) know_false)
        show know_true
        ]
      ]


    ; replace the knowledge of the action
    set action_knowledge replace-item button_chosen action_knowledge (list know_true know_false)

    ; and finally, set vision_indexes as the new observation
    set observation vision_indexes; TODO: what if after walk, there is no information about new local pathes?
    ]

end



to communicate
   ; to combine all the action_button of every agent, getting a learning result:action_communication.
   let integration []

   foreach n-values (length buttons) [?][
   ; for each agent, we take the all their knowledge
   let know_true []
   let know_false []
   ask turtles [
     set know_true (remove-duplicates sentence know_true first (item ? action_knowledge))
     set know_false (remove-duplicates sentence know_false last (item ? action_knowledge))
     ]
   ; TODO: extract information from know_false to know_true

   set integration (lput (list know_true know_false) integration)
   ]

   ask turtles [
     set action_knowledge integration
     ]
end




;==============variable related to the setup of buttons=============================================================================
;goal: a list with two lists, the first list indicates the "on" positions, the second indicates "off" positions.
;solution_length:the number of buttons that leads to the pattern. The last one button cleans the random sets in the previous buttons.
;noise: number of random elements in each solution button.
;noise_vals:a list consisting of the randomly chosen position in the goal_combination list, with the length eq to noise.
;choose_num: the extent to which a button's result is similar to the goal.An absolte value.
;chosen: a list consisting of the elements in the goal_combination that is chosen to a solution button.
;buttons: the matrix consisting of lists, each of which is one button that leads to the pattern.
;disturbing_buttons: the matrix consisting of lists, each of which is one button that leads to anything but the pattern.
;buttons: the matrix consisting of lists, each of which is one button, with the buttons leading to the solution coming first.
;noise_dis: number of random elements in each disturbing button.
;noise_dis_vals: list consisting of lights (position) related to the environment.But they have notthing to do with the goal.
;==============the design of the buttons========================================================================
;Every agent has the same number of buttons, so the total number of buttons in the model is decided by the multiplication of (button_each * num_agents).
;We set first half of the total buttons to be the solution, i.e. a list of buttons leading to the goal. ( if the total number of the buttons is odd, we set first ( half + 0.5 ) buttons to be the solution.
;All the solutions buttons form the matrix called "buttons", the remaining buttons form the matrix called "disturbing_buttons".
;Each solutions buttons in the matrix "buttons" except the last one , gets equal amount part of similarity to the goal pattern, but different elements of the goal pattern.
;The last button in the solution matrix is set to tidy up all the indifference to the goal pattern, by performing/pressing the pervious buttons in sequene and compared the outcome with the goal pattern.
;All of the buttons in the matrix is nothing more than randomly set buttons.
;All the buttons form the matrix called "buttons", in which the solution buttons come before the remaining buttons. And the sequence in this matrxi determines the serial number for the button.



;==============the assignment of buttons to turtles============================================================
;Randomly assigned. The serial number for the button is the sequence of the buttons in the matrix "button_all", it is always that the first half or first (half + 0.5) buttons is the solution buttons.
;


to assign-buttons; randomly assign the buttons to the turtles
   let remain_bt buttons; variables remained when assigning buttons to agents one by one
   ask turtles[
   set buttons_assigned []
    foreach n-values button_each [?][
    let n_button ( random  (length remain_bt ))
    set buttons_assigned lput ((position  (item n_button remain_bt) buttons )  + 1 ) buttons_assigned
    set remain_bt (remove (item n_button remain_bt) remain_bt )

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

tick
end

;==================================bidding and planning===========================================
; datatype for A* planning
; a tuple of the followings:
; the hour
; the bidding value
; the plan so far
; the world

to bid ; calculate the bidding value for each agent for each action
  ;a new bidding round
  reset_bidding

  ; simple planning algorithm
  ; simple-bidding


  ;A* planning algorithm

  ; initialise the planning part
  ; 1) construct an instance of the date structure
  ask turtles [
  let world_now represent_visable_world
  let current_node obtain_node hour (calculate_bidding world_now) buttons_chosen_before world_now
  let result (a_star_planning current_node)

  ]
end

; the result is a pair of action and the bidding value
to-report a_star_planning [current_node]
  ; first, obtain the node with the best bidding value
  let stack (fput current_node [])
  set stack (a_star_planning_rec stack)
  let best_final_node (find_best_node stack)
  report (list 0 0)
end

to-report a_star_planning_rec [stack]


  report stack
end


to-report find_best_node [stack]
  ; obtain the node with the best bidding value
  report first stack
end

to-report obtain_node [h v p w]
  ; TODO: this method can be simplied using task
  let node (fput w [])
  set node (fput p node)
  set node (fput v node)
  set node (fput h node)
  report node

end


to reset_bidding
  set bidding []
  foreach buttons [
    set bidding (fput 0 bidding)
    ]
end

;a simple bidding methods where each agent think only one step ahead
to simple-bidding
  ask turtles [
    ; for each action
    foreach (n-values length buttons [?]) [
      let world_now represent_visable_world ;a representation of the world from the agent knows
      let world_after (expected_local_world world_now (item ? action_knowledge)); ; perform the action according to the knowledge of the action
      let bidding_value calculate_bidding world_after
      if (bidding_value > (item ? bidding)) [set bidding replace-item ? bidding bidding_value]
    ]
  ]
end

to-report represent_visable_world ; to give the index of visable patches (for performing action in mind later)
  let rep []
  ; first obtain the list of visable patches
  let vision (patches in-cone-nowrap vision_radius 360)

  ask vision[
    ifelse (pcolor = black)
    [set rep (fput ((pycor * width + pxcor ) * -1) rep)]; if it is black
    [set rep (fput (pycor * width + pxcor) rep)]; otherwise it is green, positive number
  ]

  ; obtain vision index
  report rep
end

to-report expected_local_world [world act]; to perform an action according to the agent's knowledge
  ;show "the knowledge of the action is as follows"
  ;show act
  ; extract the certain effect of this action
  ; first the know_true part

  let expected []

  let know_true first act;
  let know_false last act;

  foreach world [
    ; ==== the certain part of the expected world
    ; first, there is no effect,
    ifelse ((member? (3 * ? + 2) know_true) or (member? (-3 * ? + 2) know_true))
    [set expected (fput ? expected)] ; if the agent knows that the action has no effect on this patch then it keeps it in the expected world
    [
      if ((? > 0) and (member? (3 * ?) know_true))[set expected (fput ? expected)]
      if ((? > 0) and (member? (3 * ? + 1) know_true))[set expected (fput (-1 * ?) expected)]
      if ((? < 0) and (member? (-3 * ? + 1) know_true))[set expected (fput ? expected)]
      if ((? < 0) and (member? (-3 * ?) know_true))[set expected (fput (-1 * ?) expected)]

      ]
    ; the rest is not sure for the agent.
    ]

  report expected
end

to-report calculate_bidding [world_after] ;  compare it with the goal and calculate a value for bidding
  let goal_on first goal
  let goal_off last goal
  let bidding_value 0
  foreach world_after[
     if (member? ? goal_on) [set bidding_value (bidding_value + 1)]
     if (member? ? goal_off) [set bidding_value (bidding_value - 1)]
     if (member? (? * -1) goal_off) [set bidding_value (bidding_value + 1)]
     if (member? (? * -1) goal_on) [set bidding_value (bidding_value - 1)]
    ]
  ; TODO: add the learning values on

  report bidding_value
end



to walk
  ask turtles [fd 1]
end

; TODO: button generation can be done using "shuffle"
; TODO: random buttons are simply too random and looks ugly
; TODO: ask the agent to press the button, not the observer
; change all the "knowledge" to belief
@#$#@#$#@
GRAPHICS-WINDOW
725
44
1292
631
-1
-1
15.625
1
10
1
1
1
0
0
0
1
0
31
0
31
1
1
1
ticks
30.0

SLIDER
306
139
583
172
button_each
button_each
1
10
2
1
1
NIL
HORIZONTAL

BUTTON
199
339
351
372
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
353
340
472
373
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
22
323
182
385
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
21
139
298
172
num_agents
num_agents
2
7
3
1
1
NIL
HORIZONTAL

SLIDER
22
181
300
214
vision_radius
vision_radius
0
10
4
1
1
NIL
HORIZONTAL

MONITOR
497
395
580
440
Day
day
17
1
11

SLIDER
314
183
595
216
num_hours
num_hours
(ceiling (button_each * num_agents / 2)) + 1
ceiling button_each * num_agents
6
1
1
NIL
HORIZONTAL

MONITOR
479
35
685
84
NIL
goal
17
1
12

BUTTON
23
395
128
428
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
139
394
244
427
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
259
393
364
426
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
379
395
484
428
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
15
512
186
573
button of Agent 0
[buttons_assigned] of turtle 0
17
1
15

INPUTBOX
9
31
189
91
pattern_name
Smile.txt
1
0
String

MONITOR
201
512
371
573
button of Agent 1
[buttons_assigned] of turtle 1
17
1
15

MONITOR
386
512
562
573
button of Agent 2
[buttons_assigned] of turtle 2
17
1
15

BUTTON
190
36
339
92
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

TEXTBOX
19
481
169
499
Agent 0
15
0.0
1

TEXTBOX
219
480
369
498
Agent 1\n
15
0.0
1

TEXTBOX
399
481
549
499
Agent 2
15
0.0
1

MONITOR
500
322
642
383
Current Action
button_chosen
17
1
15

SLIDER
22
222
298
255
noise
noise
0
13
6
1
1
NIL
HORIZONTAL

BUTTON
344
36
468
93
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
594
136
694
181
Total buttons
num_agents * button_each
17
1
11

MONITOR
587
395
675
440
hour
hour
17
1
11

MONITOR
28
612
634
657
plan so far
buttons_chosen_before
17
1
11

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
