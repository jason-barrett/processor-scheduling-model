;; Agent-Based Modeling
;; Stochastic Autonomous-Process Approach to CPU Scheduling
;; Summer 2023

breed [ processes process ]
breed [ cpus cpu ]

globals [
  ;; State constants.
  CPU-INST
  IO-INST

  ;; The probability of any process's yielding the CPU on any tick will be a weighted combination of factors including:
  ;;  * the priority of the process
  ;;  * the composition of the upcoming set of instructions
  ;;  * the time the process has had the CPU already
  ;; These variables control the weights each of those factors are given.  They should sum to 1, and be set once,
  ;; during setup.
  priority-weight
  lookahead-weight
  time-on-cpu-weight


  ;; List of the number of ticks taken, per process, to finish.
  ticks-by-process

  ;; List of the process priorities (saved here to survive the death of the process).
  priorities-by-process

  ;; List of the numbers of CPU instructions completed per process (also saved to survive the death of the
  ;; process.
  cpu-instructions-by-process

  ;; Current (approximate) CPU instruction throughput in terms of instructions per tick.  This will be measured
  ;; across all CPUs if there are more than one.
  cpu-instruction-throughput

  ;; Measure of what the 'ideal' throughput would be across all processes and CPUs.
  ideal-throughput
]

processes-own [
  ;; A workload is represented as a list of points at which it transitions from CPU instructions (where
  ;; it always starts) to I/O waits, and back.
  workload

  ;; The progress pointer is a state variable that indicates where in the workload this process is.
  progress-pointer

  ;; A temporary state flag that prevents a process from yielding and being granted the CPU in the same tick.
  yielded-this-tick?

  ;; The priority of this process.  Lower numbers = higher priority.
  priority

  ;; Track the amount of time that the process has held a CPU.  This should increment on every tick when the process
  ;; has a CPU, and reset to 0 when the process gives up the CPU.
  time-on-cpu
]

cpus-own [
  ;; The current process that is linked to and 'owns' this CPU, referenced by its who number.
  current-process

  ;; Track the context switch state as the number of ticks until the CPU is ready for use by a process that's just
  ;; switched onto it.
  switch-state

  ;; For evaluation of metrics, store the number of ticks this CPU did not spend doing useful work.
  ticks-spent-idle
]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Workflow / lifecycle routines.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Setup routine.
;; Initialize all CPU and process member variables.
to setup
  clear-all

  ;; Set permanent values for state constants.
  set CPU-INST 0
  set IO-INST 1

  ;; Set the weights to use when calculating an overall priority of yielding the CPU.
  set-yield-weights

  ;; Reset the global list variables to all-zeroes lists.
  set ticks-by-process n-values num-processes [ 0 ]
  set priorities-by-process n-values num-processes [ 0 ]
  set cpu-instructions-by-process n-values num-processes [ 0 ]

  ;; Set the default share for the CPU icon.
  set-default-shape cpus "flag"

  create-processes num-processes [
    set workload initialize-workload
    set progress-pointer 0
    render-workload get-x-position
    set hidden? true
    set yielded-this-tick? false

    set priority who
    set priorities-by-process replace-item who priorities-by-process priority

    set time-on-cpu 0
  ]

  ;; Create the CPUs.  Start with one and make this variable later.
  ;;
  ;; Note that who numbers are unique across breeds, so the CPUs can't be referred to starting with who
  ;; number 0.
  create-cpus 1 [

    set current-process highest-priority-free-process
    create-link-with highest-priority-free-process

    position-cpu-icon

    set ticks-spent-idle 0
    set switch-state 0
  ]

  ;; Show a legend on the screen.
  show-legend

  ;; Don't show the links on the screen.
  ask links[
    hide-link
  ]

  reset-ticks

end  ;; setup


to go

  ;; Step 1.  Progress the workloads.
  ask processes [
    advance-workload
    render-workload get-x-position

    if is-workload-complete? = true [
      finalize-workload  ;; This should release the CPU the process has been running on.
      die
    ]
  ]

  ;; Step 2.  Track statistics and update agent state.
  set ideal-throughput count cpus
  set cpu-instruction-throughput (reduce + cpu-instructions-by-process) / (ticks + 1)

  ask processes with [ get-my-cpu != nobody ] [
    set time-on-cpu time-on-cpu + 1
  ]

  ask cpus with [ get-my-process != nobody ] [
    ;; If the CPU is not ready, taking a switch penalty, then it is idle.
    ifelse not is-cpu-ready? [
      set ticks-spent-idle ticks-spent-idle + 1
    ] [
      ;; Determine whether the linked process just did an IO or a CPU instruction.  A ready CPU is idle if it's
      ;; sitting there while its process waits for I/O.
      if count link-neighbors with [ workload-activity-at-step (progress-pointer - 1) = IO-INST ] = 1 [
        set ticks-spent-idle ticks-spent-idle + 1
      ]
    ]

    ;; If we're tracking a context switch state penalty, update it here.
    advance-switch-state
  ]

  ;; Step 3. Stop the model once every process has completed and died.
  if count processes = 0 [
    finalize-model-run
    stop
  ]


  ;; Step 4.  Any processes holding CPUs may consider yielding them here.  No process should yield the CPU if it is the only
  ;; process still running.  No process should yield the CPU if it is still in the process of context switching TO that
  ;; CPU.
  if count processes > 1 [
    ask processes with [ get-my-cpu != nobody ] [
      let my-cpu get-my-cpu
      let cpu-ready? false
      ask my-cpu [ set cpu-ready? is-cpu-ready? ]
      if random-float 1.0 < overall-yield-probability and cpu-ready? [

        yield-cpu
        set yielded-this-tick? true
        set time-on-cpu 0
      ]
    ]
  ]


  ;; Step 5.  Handle allocation of free CPUs for the next tick.
  ask cpus with [ get-my-process = nobody ] [
    (ifelse free-cpu-allocation-strategy = "Highest Priority" [
      allocate-next-highest-priority
    ]
    free-cpu-allocation-strategy = "Random" [
      allocate-random
    ])

    position-cpu-icon
    set switch-state switch-penalty
  ]


  ;; Clear per-tick state.
  ask processes [
    set yielded-this-tick? false
  ]


  ;; Time marches on.
  tick
end   ;; go


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Processor-called methods and reporters.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generate a pseudo-random workload based on the given cpu-bound-percentage.
to-report initialize-workload
  let avg-run-length workload-length / 10
  let std-run-length 3
  let workload-list []

  ;; We'll represent the workload as a list of activities (CPU-INST or IO-INST) for each step.
  ;;
  ;; Start by building a list of the points in the workload where the activity changes,  Strictly speaking the
  ;; workload should probably always start and end on a run of CPU instructions.  Implementing this is a potential
  ;; enhancement.
  let workload-pointer 0
  while [ workload-pointer < workload-length ] [
    ;; Make sure the workload pointer advances at least 1, so there are no stretches of zero (or fewer!) CPU or I/O
    ;; instructions.
    let workload-pointer-increment round random-normal avg-run-length std-run-length
    if workload-pointer-increment < 1 [ set workload-pointer-increment 1 ]

    set workload-pointer workload-pointer + workload-pointer-increment
    set workload-list lput workload-pointer workload-list
  ]

  ;; Iterate over the list of change points and fill in the list of activities
  let my-pointer 0
  let current-activity CPU-INST
  let workload-array []
  repeat workload-length [
    set workload-array lput current-activity workload-array

    set my-pointer my-pointer + 1
    if not empty? workload-list and my-pointer = first workload-list [
      set current-activity (current-activity + 1) mod 2
      set workload-list but-first workload-list
    ]
  ]

  ;; The last iteration went beyond the end of the list, so truncate it by 1.
  report workload-array

end


;; Render the workload visually on the screen, using colored patches to represent CPU time and I/O time.
;; This is called by a process, which only has one workload to render.
to render-workload [ xpos ]
  let current-activity processor-state

  ;; Make a copy of the process's workload being rendered, because we're going to destroy it as we go.
  let my-workload workload
  let my-pointer progress-pointer

  ;; Start the rendering a couple of patches from the top to make way for a CPU icon.
  let ypos max-pycor - 2

  ;; Clean the slate.
  ask patches with [ pxcor = xpos ] [ set pcolor black ]

  ;; Remove elements of the workload list prior to the current progress pointer.
  foreach workload[
    x -> if x <= progress-pointer [ set my-workload but-first my-workload ]
  ]

  ;; Iterate over this window.
  repeat (workload-length - progress-pointer) [
    ask patch xpos ypos [
      ifelse current-activity = CPU-INST [ set pcolor red ][ set pcolor blue ]
    ]

    ;; Check if the current activity needs to change
    set my-pointer my-pointer + 1
    set current-activity workload-activity-at-step my-pointer
    ;; Don't render past the end of the screen.
    if ypos = min-pycor [ stop ]

    set ypos ypos - 1
  ]

end


;; Get the horizontal position where this process will render on the screen.
;; This is called by a process.
to-report get-x-position
  report who * 2
end


;; Report the CPU that this process is using, or Nobody if the process is not currently allocated a CPU.
;; This is called by a process.
to-report get-my-cpu
  ifelse count link-neighbors = 1 [ report one-of link-neighbors ] [ report nobody ]

end


;; Determine the processor's current state (CPU or I/O), given its workload and progress pointer.
;; This is called by a process.
to-report processor-state
  report workload-activity-at-step progress-pointer
end


;; Reports true if the processor has completed its workload, false if it has not.
;; This is called by a process.
to-report is-workload-complete?
  ifelse progress-pointer >= workload-length[ report true ] [ report false ]
end


;; Move forward one step in the workload, if possible (i.e., if I don't need a CPU and not have one)
;; This is called by a process.
to advance-workload
  if progress-pointer < workload-length [
    ifelse processor-state = IO-INST [
      set progress-pointer progress-pointer + 1
    ] [
      ;; CPU-INST case, only advance if on a ready CPU
      let my-cpu get-my-cpu
      let ready-cpu? false

      if my-cpu != nobody [ ask my-cpu [ set ready-cpu? is-cpu-ready? ] ]
      if ready-cpu? [
        set progress-pointer progress-pointer + 1

        ;; Track the fact that I just completed a CPU instruction.
        let cpu-instructions-this-process item who cpu-instructions-by-process
        set cpu-instructions-this-process cpu-instructions-this-process + 1
        set cpu-instructions-by-process replace-item who cpu-instructions-by-process cpu-instructions-this-process
      ]
    ]
  ]
end


;; Gets the workload instruction type (CPU-INST or IO-INST) at a given step in the workload (must be between 0 and
;; workload-length - 1).
;; This is called by a process.
to-report workload-activity-at-step [ step ]
  if step < 0 or step >= workload-length [
    ;; This is an error.
    report -1
  ]

  report item step workload
end


;; Special processing for reaching the end of a workload.
;;
;; At a minimum, release the CPU the process has been using.  Fireworks optional.
;; This is called by a process.
to finalize-workload
  ask my-links [ die ]

  ;; Record the number of ticks the process took to finish.
  set ticks-by-process replace-item who ticks-by-process ticks
end


;; Calculate the probability of yielding the CPU, based on the priority of the current process.
;; This is called by a process.
to-report yield-probability-by-priority
  ;; This process needs to know its ranking in priority among other current running processes.
  ;;
  ;; Let's say we have a 10% of yielding the CPU if we're the highest priority process, 90% if the lowest, and the others
  ;; are evenly distributed in between.
  let process-list sort-on [ priority ] processes                     ;; List of processes
  let priority-list remove-duplicates map [ priority ] process-list   ;; Sorted list of unique priorities

  ;;If somehow this was called by the only active CPU, it will not yield.
  if length process-list = 1 [ report 0.0 ]

  let idx 0
  while [ priority != item idx priority-list ] [
    set idx idx + 1
  ]

  let yield-probability 0.1 + (idx * ((0.9 - 0.1) / (length process-list - 1)))

  report yield-probability

end


;; Calculate the probability of yielding the CPU based on the upcoming series of instructions.  For starters, base
;; the yield probability simply on the propotion of instructions in the lookahead window that are CPU vs. I/O waits.
;; This is called by a process.
to-report yield-probability-by-lookahead-window
  let my-pointer progress-pointer
  let my-workload workload

  ;; Look at the next N instructions, but stop if the progress pointer would exceed the workflow length.
  let total-activities 0
  let io-activities 0
  let idx 0
  while [ idx < lookahead-window and my-pointer < workload-length ] [
    set total-activities total-activities + 1
    if workload-activity-at-step my-pointer = IO-INST [
      set io-activities io-activities + 1
    ]

    set my-pointer my-pointer + 1
    set idx idx + 1
  ]

  if total-activities = 0 [ report 0.0 ]

  report (io-activities / total-activities)

end


;; Calculate the probability of yielding the CPU based on the time the process has had the CPU.
;; This is called by a process.
to-report yield-probability-by-time-on-cpu
  let max-time-on-cpu 10  ;; This could be a parameter.

  report (time-on-cpu / max-time-on-cpu)

end


;; Calculate the overall probability of yielding the CPU as some combination of the probabilites due to the
;; different considerations.
;; This is called by a process.
to-report overall-yield-probability

  report (priority-weight * yield-probability-by-priority)
    + (lookahead-weight * yield-probability-by-lookahead-window)
    + (time-on-cpu-weight * yield-probability-by-time-on-cpu)
end


;; Yield the CPU.
;; This is called by a process.
to yield-cpu
  ask my-links [ die ]
end


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CPU-called methods and reporters.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Report the process that this CPU is running, or Nobody if the CPU is currently idle.
;; This is called by a CPU.
to-report get-my-process
  ifelse count link-neighbors = 1 [ report one-of link-neighbors ] [ report nobody ]

end

;; An allocation strategy that simply chooses the next highest priority process.
;; This is called by a CPU, and should only be called by a free CPU (not linked to anything).
to allocate-next-highest-priority
  create-link-with highest-priority-free-process
  ask links [
    hide-link
  ]
end


;; An allocation strategy that chooses the next process at random.
;; This is called by a CPU, and should only be called by a free CPU (not linked to anything).
to allocate-random
  create-link-with random-process
  ask links [
    hide-link
  ]
end


;; Set the x (horizontal) position of the CPU icon, based on the process it's currently linked with.  If there's
;; no process (the CPU is free), put it all the way to the left for now.
;; This is called by a CPU.
to position-cpu-icon
    let cpu-x-position min-pxcor

    ;; The process turtle at the other end of the link knows its x position, which we also want to use for the
    ;; CPU icon.  So ask it to set that variable for us.
    if count my-links = 1 [
      ask link-neighbors [ set cpu-x-position get-x-position ]
    ]
    setxy cpu-x-position max-pycor

end

;; Reports whether the CPU is ready for use, as it may be in the middle of a context switch.
;; This is called by a CPU.
to-report is-cpu-ready?
  ifelse switch-state = 0 [ report true ][ report false ]
end

;; Advances the context switch state for the called CPU.  (But never beyond 0 = ready.)
;; This process is called by a CPU.
to advance-switch-state
  if switch-state > 0 [ set switch-state switch-state - 1 ]
end


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General, or observer-called methods and reporters.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Reports the highest priority process still alive, which is eligible to take a CPU (i.e., it has not just yielded).
;; This is called by the observer.
to-report highest-priority-free-process
  ;; Remember, lower priority numbers mean higher priority.
  report min-one-of processes with [ get-my-cpu = nobody and yielded-this-tick? = false ] [ priority ]
end


;; Reports a random process still alive, which is eligible to take a CPU (i.e., it has not just yielded).
;; This is called by the observer.
to-report random-process
  report one-of processes with [ yielded-this-tick? = false ]
end

;; Calculate and report a measure of the difference between the actual histogram of times each process took to complete
;; its workload, and the time it 'should' have taken based on the relative priorities of each process.  This is a
;; measure of how closely the processes' priorities were followed.
;; This is intended to be called by the observer after the model run has ended.
to-report chi-square-completion-times-distance
  ;; The actual histogram is in the global variable ticks-by-process.  The 'ideal' histogram can be derived from the
  ;; variable priorities-by-process.
  let largest-priority max priorities-by-process  ;; This is the *lowest* priority.
  let most-ticks-taken max ticks-by-process
  let ideal-ticks-histogram n-values num-processes [ 0 ]

  let idx 0
  repeat num-processes [
    let this-priority item idx priorities-by-process
    set ideal-ticks-histogram replace-item idx ideal-ticks-histogram (this-priority * (most-ticks-taken / largest-priority))

    set idx idx + 1
  ]

  ;; Calculate the chi-square distance measure based on the actual and ideal ticks taken arrays.
  set idx 0
  let chi-sq-distance 0
  repeat num-processes [
    let num (item idx ticks-by-process - item idx ideal-ticks-histogram)
      * (item idx ticks-by-process - item idx ideal-ticks-histogram)
    let denom item idx ticks-by-process + item idx ideal-ticks-histogram
    set chi-sq-distance chi-sq-distance + (num / denom)
  ]

  report sqrt chi-sq-distance

end

;; This command sets the weights that will be given to different factors when a process considers whether to yield the
;; CPU, based on the chooser input yield-strategy.
;; This command is called by the observer.
to set-yield-weights
  (ifelse
    yield-strategy = "Equal Weight" [
      set priority-weight 0.34
      set lookahead-weight 0.33
      set time-on-cpu-weight 0.33
    ]
    yield-strategy = "Favor Priority" [
      set priority-weight 0.6
      set lookahead-weight 0.2
      set time-on-cpu-weight 0.2
    ]
    yield-strategy = "Favor Lookahead" [
      set priority-weight 0.2
      set lookahead-weight 0.6
      set time-on-cpu-weight 0.2
    ]
    yield-strategy = "Favor Time On CPU" [
      set priority-weight 0.2
      set lookahead-weight 0.2
      set time-on-cpu-weight 0.6
    ]
  )
end


;; Show a legend on the screen to illustrate the colors used to represent different workload activities.
to show-legend
  ask patch (-6) (max-pycor - 2) [
    set pcolor red
  ]

  ask patch (-9) (max-pycor - 2) [
    set plabel "CPU Instructions"
  ]

  ask patch (-6) (max-pycor - 4) [
    set pcolor blue
  ]

  ask patch (-9) (max-pycor - 4) [
    set plabel "I/O Waits"
  ]
end

;; This command performs any final processing we want to do at the end of the model run.
to finalize-model-run
  output-print "CPU Instruction Throughput: "
  output-print cpu-instruction-throughput
  output-print ""
  output-print "Chi-Square Completion Times Distance: "
  output-print chi-square-completion-times-distance

end
@#$#@#$#@
GRAPHICS-WINDOW
296
22
733
460
-1
-1
13.0
1
10
1
1
1
0
1
1
1
-16
16
-16
16
0
0
1
ticks
30.0

SLIDER
8
61
231
94
cpu-bound-percentage
cpu-bound-percentage
0
1
0.5
0.01
1
NIL
HORIZONTAL

SLIDER
8
104
180
137
workload-length
workload-length
20
200
100.0
1
1
NIL
HORIZONTAL

BUTTON
63
349
136
382
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

BUTTON
166
349
229
382
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

SLIDER
9
17
181
50
num-processes
num-processes
1
8
8.0
1
1
NIL
HORIZONTAL

CHOOSER
6
231
230
276
free-cpu-allocation-strategy
free-cpu-allocation-strategy
"Highest Priority" "Random"
0

SLIDER
6
189
195
222
lookahead-window
lookahead-window
1
20
4.0
1
1
NIL
HORIZONTAL

SLIDER
7
148
179
181
switch-penalty
switch-penalty
0
5
0.0
1
1
NIL
HORIZONTAL

PLOT
768
27
1020
177
CPU Instruction Throughput
Time
Throughput
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot cpu-instruction-throughput"

CHOOSER
8
284
192
329
yield-strategy
yield-strategy
"Equal Weight" "Favor Priority" "Favor Lookahead" "Favor Time On CPU"
2

OUTPUT
768
205
1083
317
12

@#$#@#$#@
## WHAT IS IT?

This model explores the behavior of a set of processes, which are running instances of computer programs, as they share the use of one or more central processing units (CPUs).

Processes run workloads, which consist of instructions that require use of a CPU, and waits for input/output (I/O).  In this model, the workloads are represented visually, with CPU instructions in red and I/O waits in blue.

The agents in this model are:

(1) The processes, whose workloads are visible on the screen as strips of red (CPU instructions) and blue (I/O waits) patches, and

(2) The CPU, which is represented by a flag that appears atop the workload for the process that has that CPU at that time.

The environment is a computer running programs.  A process is an instance of a running program.  It is more of a featurespace environment, as the processes are not physical entities.  (The CPUs are but they are not physically in motion.)


## HOW IT WORKS

Processes have the following properties:

WORKLOAD: The set of instructions (i.e., computer program) it is to run, including interspersed runs of CPU instructions and I/O waits.  Thw workload is represented as a list of workload-length length, where each element is either the constant CPU-INST or the constant IO-INST.

PROGRESS-POINTER: This tracks where in the workload the process currently stands,

YIELDED-THIS-TICK?: A processor who has just yielded the CPU is not eligible to grab the CPU on the same tick.  This variable tracks that state.

PRIORITY: The priority of the process relative to other properties.  This is numerical, lower numbers mean higher priority.  The code sets this simply to the who number of the process, but one could experiment with other priority mixes.  Priority need not be an integer.

TIME-ON-CPU: Keeps track of the consecutive time this process has held the CPU.


CPUs have the following properties:

CURRENT-PROCESS: The process, by who number, that is currently running on the CPU.  This is not tracked currently, but could be used for display purposes.

SWITCH-STATE: When a context switch penalty is in effect, controlled by the SWITCH-PENALTY input variable, this tracks the state of the penalty for each CPU.  It is set to the penalty value on switching processes, and decremented each tick to 0.

TICKS-SPENT-IDLE: This tracks the time that a CPU spends idle, where 'idle' means running a process that waits for I/O that tick, or incurring a switch penalty.


########################################################################################

Processes take the following actions at each tick, using rules as described:

They advance their workloads.  If the process has the CPU, it may advance through a CPU instruction or an I/O wait.  Otherwise it may only advance through an I/O wait.

Those that are using a ready CPU will decide whether to yield the CPU on that tick.  If they do, then the CPU is available for another process (subject to the context switch penalty, if configured).  The processes make that decision as a weighted probability, considering the following factors:

* The priority of the process.  Higher priority processes are less likely to yield.
* The composition of the process's upcoming instructions.  Processes with a high proportion of I/O waits coming up are more likely to yield.
* The time the process has held the CPU already.  The longer it has had it, the more likely the process is to yield.


CPUs take the following actions at each tick, using rules as described:

They update statistics.

They determine whether they need to wait before running any CPU instructions, by tracking a potential context switch penalty if they have recently switched processes.

########################################################################################

The following sequence of events happens on setup (trivial actions omitted):

1. The model sets the yield weights to obey the input parameter yield-strategy.

2. The model initializes lists for statistics.

3. The model creates num-processes, initializes their workloads, and renders them on the screen, and initializes all variables and statistics.\

4. The model creates the CPU(s) and initially allocates them to the highest priority process(es)  CPU statistics are initialized as well.


The following sequence of events happens on each tick ('go') (trivial actions omitted):

1. Each process advances its workload, if it can, and updates the rendering on the screen.  If the workload completes, the process dies, after saving any state we'll need to calculate final statistics.

2. Processes and CPUs update their state and statistics based on the actions taken in (1).

3. The model checks to see if all processes have died, in which case it calculates and prints final statistics and stops the run.

4. All processes holding CPUs execute the logic that governs the decision to yield the CPU or not.

5. Any CPUs which have been yielded choose the next process that gets to use them.



## HOW TO USE IT

Use the following input controls to vary the parameters of the model.

NUM-PROCESSES: The number of processes vying for CPU time.

CPU-BOUND-PERCENTAGE: The average proportion of a workload that is spent using the CPU.

WORKLOAD-LENGTH: The time (in ticks) a workload takes (or would take, if it always had the CPU when it needed it), including both CPU instructions and I/O waits.

LOOKAHEAD-WINDOW: The number of instructions ahead the process will consider when determining the likelihood of yielding the CPU based on the upcoming proportion of instructions that use the CPU.

SWITCH-PENALTY: The number of ticks it takes after a CPU switches from one process to another before it can start running instructions for the new process.  Simulates the context switch penalty in real hardware.

FREE-CPU-ALLOCATION-STRATEGY: When a CPU becomes free (yielded, or the process using it has finished), how does it decide which process gets it next?

Highest Priority: Always goes to the next highest priority process still running.

Random: Goes to a random process.

YIELD-STRATEGY: A set of alternative strategies each process will use when deciding whether to yield the CPU on any turn.  Each strategy corresponds to a different set of weights on the yield factors listed above.

Equal Weights: No factor has preference over any others.

Favor Priority: The process's priority is given higher weight in the yield decision.

Favor Lookahead: The upcoming instruction composition is given higher weight in the yield decision.

Favor Time On CPU: The time the process has had the CPU is given higher weight in the yield decision.

######################################################################################

Look for the following output as the model runs and when it has finished.

CPU Instruction Throughput: This is shown as a graph as the model runs, and the final throughput appears in the output window when it has finished.  Throughput is measured as the number of CPU instructions processed per tick.  This is basically the reverse of the CPU idle time.  Throughput takes a 'hit' when the CPU is idle; that is, when the processor using it is waiting on I/O, or when the CPU is in the midst of a context switch.

Chi-Square Completion Times Distance: This is a measure of how closely the final distribution of times taken for each process to complete matches the distribution of process priorities.  Ideally, for instance, if two processes have priorities 1 and 2, the final completion times should be in a 1:2 ratio.  (Priorities do not have to be integers.)  This metric uses a chi-square distance calculation to assess how close the priorities ratio is to the completion times ratio.


## THINGS TO NOTICE

(suggested things for the user to notice while running the model)

## THINGS TO TRY

(suggested things for the user to try to do (move sliders, switches, etc.) with the model)

## EXTENDING THE MODEL

Accounting for multiple CPUs would be an obvious enhancement, reflecting the real world.

In the initial version, the priorities of the process differ by 1 and are simply set to the processes' who numbers.  One could set the priorities differently in code, or create a user interface to do so.  Perhaps the best strategies and inputs would be different in a world where one very high priority process shared the CPU(s) with many lower priority processes.  Priorities need not be integers.

It's also possible to experiment with different weights for the probability factors that come into the decision to yield the CPU (see above).  It would be interesting to run a Behavior Search job to use a genetic algorithm or some other AI strategy to find the 'best' weights in a variety of scenarios.

## NETLOGO FEATURES

(interesting or unusual features of NetLogo that the model uses, particularly in the Code tab; or where workarounds were needed for missing features)


## CREDITS AND REFERENCES
https://github.com/jason-barrett/processor-scheduling-model
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
NetLogo 6.2.0
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="experiment" repetitions="10" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <metric>cpu-instruction-throughput</metric>
    <metric>chi-square-completion-times-distance</metric>
    <enumeratedValueSet variable="cpu-bound-percentage">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="free-cpu-allocation-strategy">
      <value value="&quot;Random&quot;"/>
      <value value="&quot;Highest Priority&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="yield-strategy">
      <value value="&quot;Equal Weight&quot;"/>
      <value value="&quot;Favor Priority&quot;"/>
      <value value="&quot;Favor Lookahead&quot;"/>
      <value value="&quot;Favor Time On CPU&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="num-processes">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="switch-penalty">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="workload-length">
      <value value="100"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="lookahead-window">
      <value value="8"/>
      <value value="14"/>
      <value value="20"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
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
@#$#@#$#@
0
@#$#@#$#@
