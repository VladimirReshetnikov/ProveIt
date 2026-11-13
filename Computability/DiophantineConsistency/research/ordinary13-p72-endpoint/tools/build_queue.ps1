# Serial Lake queue: one `lake build <target>` per line of -Queue, in order,
# with LAKE_JOBS=1 and LEAN_NUM_THREADS=0. Stops at the first failure.
# Writes "<status> <time> <target> exit <code> secs <n>" lines to <queue>.status
# and each target's full output to <LogDir>\q.<target>.log.
param([Parameter(Mandatory)] [string] $Queue, [string] $LogDir = $env:TEMP)
$ErrorActionPreference = 'Continue'
$env:LAKE_JOBS = '1'
$env:LEAN_NUM_THREADS = '0'
Set-Location C:\ProveIt
$status = "$Queue.status"
foreach ($target in (Get-Content $Queue | Where-Object { $_.Trim() })) {
    $name = $target.TrimStart('+') -replace '^DiophantineConsistency\.', ''
    $log = Join-Path $LogDir "q.$name.log"
    $sw = [Diagnostics.Stopwatch]::StartNew()
    lake build $target *> $log
    $code = $LASTEXITCODE
    $line = '{0,-4} {1:HH:mm} {2} exit {3} secs {4}' -f ($(if ($code -eq 0) { 'OK' } else { 'FAIL' })), (Get-Date), $target, $code, [int]$sw.Elapsed.TotalSeconds
    Add-Content $status $line
    if ($code -ne 0) { Write-Output $line; exit 1 }
}
Write-Output 'QUEUE DONE'
