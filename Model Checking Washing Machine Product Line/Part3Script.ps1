# add type checking for input of user
$Heat = Read-Host -Prompt 'Input 1 if you want a washing machine with Heat, and 0 otherwise'
$Dry = Read-Host -Prompt 'Input 1 if you want a washing machine with Dry, and 0 otherwise'
$Delay = Read-Host -Prompt 'Input 1 if you want a washing machine with Delay, and 0 otherwise'

Write-Host '------------------------------------------------------------------------------------------------------------------------'
Write-Host 'The alloy instance will be opened shortly, once you are done with it, please press ctrl+c to continue running the script'
Write-Host '------------------------------------------------------------------------------------------------------------------------'
Start-Sleep -s 5


(Get-Content '.\Phase3.als')  | ForEach-Object {
    $_.replace("#Heat = 0 // Heat to change","#Heat = $Heat ").
    replace('#Dry = 0 // Dry to change',"#Dry = $Dry ").
    replace('#Delay = 0 // Delay to change',"#Delay = $Delay")
} | Out-File .\output.als -encoding ASCII


& java -cp org.alloytools.alloy.dist.jar edu.mit.csail.sdg.alloy4whole.ExampleUsingTheCompiler .\output.als 

z3 Phase3Z3.smt | Out-File -FilePath .\Z3Results.txt


$sat = (Get-Content .\Z3Results.txt)[0]

Write-Host '------------------------------------------------------------------------------------------------------------------------'
Write-Host "---------------------------------------- The corresponding z3 model is $sat --------------------------------------------"
Write-Host '------------------------------------------------------------------------------------------------------------------------'

Start-Sleep -s 2

# The goal here is to read the results of the z3 model and map every element present in the element to its corresponding element in NuSMV
# by first identifying if the element is 'true' or present, and then saving its corresponding element (if it is a state we save 
# the NuSMV state, otherwise we save the Destination of the transition, we could have saved the origin and destination of the state 
# along with the destination and then processed it to create a new transition, but for the purpose of this project and to save on resources and 
# time, we found it better to proceed in the way shown) 

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun locking () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $locking = 'Locking ,'
} else {
    $locking = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun startP () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $startP = 'Waiting'
} else {
    $startP = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun waiting () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $waiting = 'Waiting ,'
} else {
    $waiting = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun endp () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $endP = 'Washing'
} else {
    $endP = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun startw () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $startW = 'Washing'
} else {
    $startW = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun washing () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $washing = 'Washing ,'
} else {
    $washing = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun startd () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $startD = 'Drying'
} else {
    $startD = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun drying () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $drying = 'Drying ,'
} else {
    $drying = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun endD () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $endD = 'Unlocking'
} else {
    $endD = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun endW () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $endW = 'Unlocking'
} else {
    $endW = ''
}

$match = (Get-Content -Path .\Z3Results.txt  | Select-String -Pattern "  (define-fun unlocking () Bool" -Context 0,1 -SimpleMatch).LineNumber
if ((Get-Content .\Z3Results.txt)[$match] -eq '    true)') {
    $unlocking = 'Unlocking ,'
} else {
    $unlocking = ''
}

# Mapping from z3 to States : 
(Get-Content '.\Phase3.smv')  | Out-File .\output.smv -encoding ASCII

#States
if ($locking -or $waiting -or $washing -or $drying -or $unlocking){
    $states = "$locking $waiting $washing $drying $unlocking"

    $states = $states.trimend(" ,")

    (Get-Content '.\Phase3.smv')  | ForEach-Object {
        $_.replace("states : {}; --to be edited","states : {$states}; ")
    } | Out-File .\output.smv -encoding ASCII
}else{
    Write-Host "Cannot proceed as there are no States"
    Exit 
}

#StartWash and StartPrewash Transitions
if ($startW -or $startP ){
    $startW_StartP = "$startW $StartP"
    $startW_StartP = $startW_StartP.trimend(" ,")

    (Get-Content '.\Output.smv')  | ForEach-Object {
        $_.replace("            -- states = Locking : {}; to be edited","             states = Locking : {$startW_StartP};")
    } | Out-File .\output.smv -encoding ASCII
}

#EndWash and StartDry Transitions
if ($endW -or $startD ){
    $endW_startD = "$endW $startD"
    $endW_startD = $endW_StartD.trimend(" ,")

    (Get-Content '.\Output.smv')  | ForEach-Object {
        $_.replace("            -- states = Washing : {}; to be edited","             states = Washing : {$endW_startD};")
    } | Out-File .\output.smv -encoding ASCII
}

#EndPrewash Transition
if ($endP){
    (Get-Content '.\output.smv')  | ForEach-Object {
        $_.replace("            -- states = Waiting : {}; to be edited","             states = Waiting : {$endP};")
    } | Out-File .\output.smv -encoding ASCII
}

#EndDrying Transition
if ($endD){
    (Get-Content '.\Output.smv')  | ForEach-Object {
        $_.replace("            -- states = Drying : {}; to be edited","             states = Drying : {$endD};")
    } | Out-File .\output.smv -encoding ASCII
}

if  ($unlocking){
    $unlocking = $unlocking.trimend(" ,")
    (Get-Content '.\output.smv')  | ForEach-Object {
        $_.replace("            -- states = Unlocking : {}; to be edited","             states = Unlocking : {$unlocking};")
    } | Out-File .\output.smv -encoding ASCII
}

NuSMV .\output.smv