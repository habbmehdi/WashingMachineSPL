The script flow is as follows : 

1 - First, input your choice of feature 
(only 1 and 0 can be entered otherwise it will not work)

2 - An alloy instance of the corresponding model will open up, and
the result of the Property P2 will be displayed on the terminal
NOTE : For some reason the visualizer does not show some delegated link, 
but they are present in the table view
NOTE2 : view over AbstractDiagram and Link

3 - go back to the terminal and press ctrl+c to continue

4 - a Z3 model is generated and saved in Z3Results.txt, and 
a check is done to verify if the model is valid

5 - A translation is done by creating a new file, output.smv,
in which all the corresponding z3 elements have been added 

6 - The Property P3 is checked