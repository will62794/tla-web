//
// Deployment-specific configuration for Spectacle.

window.SpectacleConfig = window.SpectacleConfig || {};

//
// GitLab OAuth2 (Authorization Code + PKCE) sign-in.
//
// Lets users load private/internal specs using their existing GitLab login,
// instead of pasting a personal access token. To enable it for an instance:
//
//   1. Register a PUBLIC (non-confidential) OAuth application on that GitLab
//      instance (User Settings -> Applications, or a group's
//      Settings -> Applications) with:
//        - Redirect URI: this app's base URL (origin + path, no query/fragment),
//                        e.g. https://<group>.<pages-domain>/spectacle/
//                        (add http://127.0.0.1:8000/ as well for local dev).
//        - Scopes:       read_api  (or the narrower read_repository).
//        - Confidential: unchecked (PKCE ships no client secret to the browser).
//   2. Add the resulting Application ID below, keyed by the instance host.
//
// Hosts without an entry simply fall back to the manual access-token field.
//
window.SpectacleConfig.gitlabOAuthClientIds = {
    // "gitlab.yourdomain.com": "<paste OAuth Application ID here>",
};

// OAuth scope requested during sign-in.
window.SpectacleConfig.gitlabOAuthScope = "read_api";
