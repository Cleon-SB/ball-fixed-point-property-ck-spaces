param(
    [string]$File = 'BFPP.lean',
    [string]$MathlibRoot = 'C:\Users\cleon\MeusTeoremas\.lake\packages\mathlib',
    [string]$LeanExe = 'C:\Users\cleon\.elan\toolchains\leanprover--lean4---v4.34.0-rc2\bin\lean.exe'
)
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$packageRoot = Split-Path -Parent $MathlibRoot
$buildRoot = Join-Path $projectRoot '.lake\build\lib\lean'
New-Item -ItemType Directory -Path $buildRoot -Force | Out-Null
$libraryPaths = @($buildRoot)
foreach ($package in Get-ChildItem -LiteralPath $packageRoot -Directory) {
    $libraryPath = Join-Path $package.FullName '.lake\build\lib\lean'
    if (Test-Path -LiteralPath $libraryPath) { $libraryPaths += $libraryPath }
}
$previousLeanPath = $env:LEAN_PATH
$env:LEAN_PATH = $libraryPaths -join [IO.Path]::PathSeparator
$sourcePath = [IO.Path]::GetFullPath((Join-Path $projectRoot $File))
if (-not $sourcePath.StartsWith($projectRoot + [IO.Path]::DirectorySeparatorChar)) {
    throw 'The source must belong to this project.'
}
$relativeOutput = [IO.Path]::ChangeExtension($File, '.olean')
$outputPath = Join-Path $buildRoot $relativeOutput
$interfacePath = [IO.Path]::ChangeExtension($outputPath, '.ilean')
New-Item -ItemType Directory -Path (Split-Path -Parent $outputPath) -Force | Out-Null
Push-Location $projectRoot
try {
    & $LeanExe -o $outputPath -i $interfacePath $File
    $checkExitCode = $LASTEXITCODE
} finally {
    Pop-Location
    $env:LEAN_PATH = $previousLeanPath
}
exit $checkExitCode
