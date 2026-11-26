param(
    [Parameter(Mandatory = $true)]
    [string]$Repository,
    [string]$LeanBin
)

$ErrorActionPreference = 'Stop'
$oldPath = $env:Path
if ($LeanBin) {
    $env:Path = (Resolve-Path -LiteralPath $LeanBin).Path + [IO.Path]::PathSeparator + $env:Path
}

$modules = @('WOWII255Data', 'WOWII255', 'WOWII255Incidence', 'WOWII255PairFamily',
    'WOWII255Sharp', 'WOWII255MinimumLower', 'WOWII255Minimum', 'WOWII256', 'WOWII256Small')
$results = @{
    WOWII255 = @('WOWII255.conjecture255_false')
    WOWII255Sharp = @('WOWII255.coefficient_valid_of_le_one', 'WOWII255.exists_pair_counterexample',
        'WOWII255.sharp_coefficient')
    WOWII255MinimumLower = @('WOWII255.order_times_two_le_domination_mul_max_of_card_le_ten',
        'WOWII255.bound_of_card_le_ten')
    WOWII255Minimum = @('WOWII255.refutes_bound11', 'WOWII255.smallest_counterexample_order')
    WOWII256 = @('WOWII256.conjecture256_false')
    WOWII256Small = @('WOWII256.refutes_bound14')
}

Push-Location -LiteralPath $Repository
try {
    $revision = & git rev-parse HEAD
    if ($LASTEXITCODE -ne 0 -or $revision -ne '9097e2f90e66d2f6244209cb1c07f7120d17ec53') {
        throw '请检出 README 所列的 Formal Conjectures 基准提交。'
    }
    $olean = Join-Path (Get-Location).Path '.lake/build/lib/lean'
    New-Item -ItemType Directory -Force -Path $olean | Out-Null
    foreach ($name in $modules) {
        Write-Output "编译 $name"
        $source = Join-Path $PSScriptRoot "$name.lean"
        $output = & lake env lean -j 1 -DautoImplicit=false -DwarningAsError=true `
            -DmaxRecDepth=10000 -DmaxHeartbeats=1000000 -R $PSScriptRoot `
            -o (Join-Path $olean "$name.olean") $source 2>&1
        $compiled = $LASTEXITCODE
        $output | Write-Output
        if ($compiled -ne 0) { throw "编译失败 $name" }

        $normalized = ($output -join ' ') -replace '\s+', ' '
        foreach ($theorem in $results[$name]) {
            $expected = "'$theorem' depends on axioms: [propext, Classical.choice, Quot.sound]"
            if (!$normalized.Contains($expected)) { throw "公理检查不符 $theorem" }
        }
    }

    foreach ($name in $modules) {
        & lake env leanchecker -v $name
        if ($LASTEXITCODE -ne 0) { throw "内核重放失败 $name" }
    }
    Write-Output "$($modules.Count) 个模块已完成编译、主要结论公理审计和内核重放。"
} finally {
    Pop-Location
    $env:Path = $oldPath
}
