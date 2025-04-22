# Contributing to ZFuel

Thank you for your interest in contributing to ZFuel! This document provides guidelines and instructions for contributing to the project.

## Code of Conduct

By participating in this project, you agree to abide by the [Rust Code of Conduct](https://www.rust-lang.org/policies/code-of-conduct).

## How to Contribute

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes (`git commit -m 'Add amazing feature'`)
4. Push to the branch (`git push origin feature/amazing-feature`)
5. Open a Pull Request

## Development Setup

1. Install Rust nightly:

   ```bash
   rustup install nightly
   ```

2. Install cargo-fuzz:

   ```bash
   cargo install cargo-fuzz
   ```

3. Clone your fork:
   ```bash
   git clone https://github.com/your-username/zfuel.git
   cd zfuel
   ```

## Testing

All contributions must pass the test suite:

```bash
# Run all tests
make all

# Run specific test types
make test    # Unit tests
make fuzz    # Fuzz tests
```

## Code Style

- Follow Rust's standard formatting:

  ```bash
  cargo fmt
  ```

- Run clippy checks:
  ```bash
  cargo clippy
  ```

## Documentation

- Update documentation for any new features or changes
- Include examples in doc comments
- Update the CHANGELOG.md for significant changes

## Pull Request Process

1. Ensure all tests pass
2. Update documentation as needed
3. Update CHANGELOG.md
4. The PR will be reviewed by maintainers
5. Address any feedback
6. Once approved, it will be merged

## Reporting Issues

When reporting issues, please include:

- Description of the problem
- Steps to reproduce
- Expected behavior
- Actual behavior
- Environment details (Rust version, OS, etc.)

## Feature Requests

For feature requests:

- Describe the feature
- Explain why it's valuable
- Provide example usage if possible

## Security

If you discover a security vulnerability, please email security@example.com instead of creating a public issue.

## License

By contributing, you agree that your contributions will be licensed under the project's Apache License 2.0.
