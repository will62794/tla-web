// @ts-check
import { test, expect } from '@playwright/test';

// 
// Basic UI tests for the TLA+ explorer interface.
// 

test('two-phase-basic', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/TwoPhase.tla&initPred=Init&nextPred=Next&constants%5BRM%5D=%7Brm1%2Crm2%2Crm3%7D');
  
    // Expect a title "to contain" a substring.
    // await expect(page).toHaveTitle(/Playwright/);
    await expect(page.getByText('Choose Initial State')).toBeVisible();

    let nextStateChoices;
    let stateChoice;
    let traceStates;

    nextStateChoices = page.getByTestId('next-state-choice');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 1 states in the trace.
    await expect(traceStates).toHaveCount(1, { timeout: 6000 });

    nextStateChoices = page.getByTestId('action-choice-param');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 2 states in the trace.
    await expect(traceStates).toHaveCount(2, { timeout: 6000 });
  });

// Next == \E p \in P : SetLeft(p) \/ SetRight(p) \/ Clear(p) should be
// shown as three separate actions, each parameterized by p.
test('exists-over-disjunction', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/exists_over_disjunction.tla&initPred=Init&nextPred=Next&constants%5BN%5D=5');

    await expect(page.getByText('Choose Initial State')).toBeVisible();

    let nextStateChoices = page.getByTestId('next-state-choice');
    await expect(nextStateChoices).toHaveCount(1, { timeout: 6000 });
    await nextStateChoices.nth(0).click();

    let traceStates = page.getByTestId('trace-state-elem');
    await expect(traceStates).toHaveCount(1, { timeout: 6000 });

    const actionName = (name) => page.locator('.action-choice-name').filter({ hasText: new RegExp(`^${name}$`) });
    const actionParams = (name) => actionName(name).locator('xpath=ancestor::tr[1]').getByTestId('action-choice-param');

    await expect(actionName('SetLeft')).toHaveCount(1, { timeout: 6000 });
    await expect(actionName('SetRight')).toHaveCount(1);
    await expect(actionName('Clear')).toHaveCount(1);

    // Nothing is set yet, so every p can set either side, and nobody can clear.
    await expect(actionParams('SetLeft')).toHaveCount(5);
    await expect(actionParams('SetRight')).toHaveCount(5);
    await expect(actionName('Clear')).toHaveClass(/action-choice-disabled/);

    await actionParams('SetLeft').filter({ hasText: '(1)' }).click();
    await expect(traceStates).toHaveCount(2, { timeout: 6000 });

    await actionParams('SetRight').filter({ hasText: '(1)' }).click();
    await expect(traceStates).toHaveCount(3, { timeout: 6000 });

    // Only 1 has both sides set, so it is the only one that can clear.
    await expect(actionParams('Clear')).toHaveCount(1, { timeout: 6000 });
    await expect(actionParams('Clear')).toHaveText('(1)');
});

test('enabled-any-branch', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/enabled_any_branch.tla&initPred=Init&nextPred=Next');

    await expect(page.getByText('Choose Initial State')).toBeVisible({timeout: 6000});

    let nextStateChoices = page.getByTestId('next-state-choice');
    await expect(nextStateChoices).toHaveCount(1, { timeout: 6000 });
    await nextStateChoices.nth(0).click();

    let traceStates = page.getByTestId('trace-state-elem');
    await expect(traceStates).toHaveCount(1, { timeout: 6000 });

    let actionChoices = page.locator('[data-testid="action-choice-param"], [data-testid="next-state-choice"]');
    await expect(actionChoices).toHaveCount(1, { timeout: 6000 });
    await actionChoices.nth(0).click();

    await expect(traceStates).toHaveCount(2, { timeout: 6000 });
});
  
  test('lockserver-basic', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/lockserver.tla');
  
    // Expect a title "to contain" a substring.
    await expect(page.getByTestId('set-config-button')).toBeVisible();

    let constServerInput = page.getByTestId('const-val-input-Server');
    await constServerInput.fill('{s1,s2}');

    let constClientInput = page.getByTestId('const-val-input-Client');
    await constClientInput.fill('{c1,c2}');

    // Set the constants.
    await page.getByTestId('set-config-button').click();

    // Now we should be on the state selection pane.
    await expect(page.getByText('Choose Initial State')).toBeVisible();

    let nextStateChoices;
    let stateChoice;
    let traceStates;

    nextStateChoices = page.getByTestId('next-state-choice');
    // Expect 1 initial state.
    await expect(nextStateChoices).toHaveCount(1, { timeout: 6000 });
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 1 states in the trace.
    await expect(traceStates).toHaveCount(1, { timeout: 6000 });

    nextStateChoices = page.getByTestId('action-choice-param');
    // Expect 4 distinct enabled actions.
    await expect(nextStateChoices).toHaveCount(4, { timeout: 6000 });

    // Find the action choice with text "c1"
    const c1s2Choice = nextStateChoices.filter({ hasText: 'c1' }).filter({ hasText: 's2' });
    await expect(c1s2Choice).toHaveCount(1);
    await c1s2Choice.nth(0).click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 2 states in the trace.
    await expect(traceStates).toHaveCount(2, { timeout: 6000 });

    // TODO: Checking actual state values.
    // await expect(traceStates.nth(1)).toHaveText('s2');
    // await expect(traceStates.nth(1)).toHaveText('FALSE');
  });

test('reset-trace-functionality', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/TwoPhase.tla&initPred=Init&nextPred=Next&constants%5BRM%5D=%7Brm1%2Crm2%2Crm3%7D');
  
    // Wait for the initial state selection to be visible
    await expect(page.getByText('Choose Initial State')).toBeVisible();

    let nextStateChoices;
    let stateChoice;
    let traceStates;

    // Step 1: Choose initial state
    nextStateChoices = page.getByTestId('next-state-choice');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 1 state in the trace
    await expect(traceStates).toHaveCount(1, { timeout: 6000 });

    // Step 2: Take first step forward
    nextStateChoices = page.getByTestId('action-choice-param');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 2 states in the trace
    await expect(traceStates).toHaveCount(2, { timeout: 6000 });

    // Step 3: Take second step forward
    nextStateChoices = page.getByTestId('action-choice-param');
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 3 states in the trace
    await expect(traceStates).toHaveCount(3, { timeout: 6000 });

    // Step 4: Click the Reset button
    await page.getByTestId('trace-reset-button').click();

    // Step 5: Verify that the trace is now empty (back to initial state selection)
    await expect(page.getByText('Choose Initial State')).toBeVisible();
    
    // Verify that there are no trace states
    traceStates = page.getByTestId('trace-state-elem');
    await expect(traceStates).toHaveCount(0, { timeout: 6000 });
});


test('two-phase-alt-init-next-defs', async ({ page }) => {
    await page.goto('http://localhost:3000/#!/home?specpath=./specs/TwoPhase_alt.tla&initPred=HInit&nextPred=HNext');
  
    // Now we should be on the state selection pane.
    await expect(page.getByText('Choose Initial State')).toBeVisible();

    let nextStateChoices;
    let stateChoice;
    let traceStates;

    nextStateChoices = page.getByTestId('next-state-choice');
    // Expect 1 initial state.
    await expect(nextStateChoices).toHaveCount(1, { timeout: 6000 });
    stateChoice = nextStateChoices.nth(0);
    await stateChoice.click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 1 states in the trace.
    await expect(traceStates).toHaveCount(1, { timeout: 6000 });

    nextStateChoices = page.getByTestId('action-choice-param');
    // Expect 4 distinct enabled actions.
    await expect(nextStateChoices).toHaveCount(4, { timeout: 6000 });

    // Find the action choice with text "c1"
    const c1s2Choice = nextStateChoices.filter({ hasText: 'rm1' });
    await expect(c1s2Choice).toHaveCount(2);
    await c1s2Choice.nth(0).click();
    traceStates = page.getByTestId('trace-state-elem');

    // Should now have 2 states in the trace.
    await expect(traceStates).toHaveCount(2, { timeout: 6000 });

    // TODO: Checking actual state values.
    // await expect(traceStates.nth(1)).toHaveText('s2');
    // await expect(traceStates.nth(1)).toHaveText('FALSE');
  });

// let si_url_params = 'specpath=./specs/SnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt0%2Ct1%2Ct2%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D="Empty"'
// test('snapshot-isolation-basic', async ({ page }) => {
//     await page.goto('http://127.0.0.1:8000/#!/home?' + si_url_params);
  
//     // Expect a title "to contain" a substring.
//     // await expect(page).toHaveTitle(/Playwright/);
//     await expect(page.getByText('Choose Initial State')).toBeVisible();

//     let nextStateChoices;
//     let stateChoice;
//     let traceStates;

//     nextStateChoices = page.getByTestId('next-state-choice');
//     stateChoice = nextStateChoices.nth(0);
//     await stateChoice.click();
//     traceStates = page.getByTestId('trace-state-elem');

//     // Should now have 1 states in the trace.
//     await expect(traceStates).toHaveCount(1, { timeout: 6000 });

//     nextStateChoices = page.getByTestId('action-choice-param');
//     stateChoice = nextStateChoices.nth(0);
//     await stateChoice.click();
//     traceStates = page.getByTestId('trace-state-elem');

//     // Should now have 2 states in the trace.
//     await expect(traceStates).toHaveCount(2, { timeout: 6000 });
//   });
