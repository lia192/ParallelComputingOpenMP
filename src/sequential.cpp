#include <bits/stdc++.h>

struct Assignment {
  /// arr - vector of legth v,
  ///     (a[i] == 1) - variable 𝑖 has been assigned the truth value “true”
  ///     (a[i] == -1) - variable 𝑖 has been assigned the truth value “false”
  std::vector<int8_t> arr;
  // num_assigned - number of assigned literals
  size_t num_assigned = 0;

  // returns size of the assignment
  size_t size() const { return arr.size(); }
};

std::ostream &operator<<(std::ostream &os, const Assignment &a) {
  os << "( ";
  for (auto x : a.arr) {
    os << static_cast<int16_t>(x) << ", ";
  }
  os << " )\n";
  return os;
}

class Matrix {
  int m_rows;
  int m_cols;
  std::vector<int8_t> m_data;

public:
  Matrix() = default;
  Matrix(int r, int c) {
    m_rows = r;
    m_cols = c;
    m_data = std::vector<int8_t>(r * c);
  }

  int cols() const { return m_cols; }
  int rows() const { return m_rows; }

  int8_t *operator[](int i) { return m_data.data() + i * m_cols; }
  int8_t get(int i, int j) const { return *(m_data.data() + i * m_cols + j); }

  friend std::ostream &operator<<(std::ostream &os, const Matrix &mat) {
    for (int i = 0; i < mat.m_rows; i++) {
      for (int j = 0; j < mat.m_cols; j++) {
        os << static_cast<int16_t>(mat.m_data[i * mat.m_cols + j]) << " ";
      }
      os << std::endl;
    }
    return os;
  }
};

struct Formula {
  Matrix matrix;
  // number of remaining literals in each clause
  std::vector<int> l;
  // num caluses
  int c() const { return matrix.rows(); }
  // num literals
  int v() const { return matrix.cols(); }

  Formula(Matrix m) : matrix(std::move(m)) {
    l.reserve(matrix.rows());
    for (int i = 0; i < matrix.rows(); i++) {
      l.push_back(std::count_if(matrix[i], matrix[i] + matrix.cols(),
                                [](int8_t x) { return x != 0; }));
    }
  }
};

std::ostream &operator<<(std::ostream &os, const Formula &f) {
  os << "matrix:\n" << f.matrix << "\n";

  os << "l:\n";
  os << "( ";
  for (auto x : f.l) {
    os << x << ", ";
  }
  os << " )\n";
  return os;
}

/// Generates random formula given:
///  \param c - number of clauses
///  \param v - number of literals
///  \param d - density
///  \param seed - seed
Formula generate_random_formula(int c, int v, float d, int seed = 1) {

  std::mt19937 generator{};
  generator.seed(seed);
  std::bernoulli_distribution ber(0.5);

  int nr_literals = static_cast<int>(c * v * d);

  std::vector<int> idx(c * v);
  std::iota(idx.begin(), idx.end(), 0);
  std::shuffle(idx.begin(), idx.end(), generator);

  Matrix F(c, v);

  for (int i = 0; i < nr_literals; ++i) {
    F[(int)(idx[i] / v)][idx[i] % v] =
        static_cast<int8_t>(ber(generator) ? 1 : -1);
  }

  return Formula{std::move(F)};
}

/// Generates 2^min(t, n) new assignments given:
/// \param a - base assignment
/// \param t - parameter with respect to which the number of assignments is
/// computed
std::vector<Assignment> generate_assignments(const Assignment &a, int t) {
  int num = std::min(t, static_cast<int>(a.size() - a.num_assigned));

  std::vector<Assignment> ret;
  ret.reserve(1 << num);

  for (int i = 0; i < (1 << num); ++i) {
    Assignment curr = a;
    for (int v = a.num_assigned; v < a.num_assigned + num; ++v) {
      if (i & (1 << (v - a.num_assigned))) {
        curr.arr[v] = 1;
      } else {
        curr.arr[v] = -1;
      }
    }
    curr.num_assigned++;
    ret.push_back(std::move(curr));
  }
  return ret;
}

/// return 1 : if it is satisfiable
/// return 0: we dont't know
/// return -1: if it is not satisfiable
/// \param a: the assignment
/// \param c: the total number of clause in F
/// \param v: number of literals
/// \param c_remaining: remaining number of clauses
/// \param l: vector of lenght c_remaining, where l[i] is the number of
/// remaining literals in clause i
int evaluate(const Formula &F, const Assignment &a, std::vector<int> &l,
             int &c_remaining) {
  int c_remaining0 = c_remaining;
  int processed_c = 0;
  int nr_satisfied_clauses = 0;
  for (int i = 0; i < F.c() && processed_c < c_remaining; i++) {
    if (l[i] == -1) {
      continue;
    }
    processed_c++;

    int processed_v = 0;
    bool clauseSatisfied = false;
    bool could_be_satisfiable = false;
    for (int j = 0; j < F.v() && processed_v < l[i]; j++) {
      int8_t literal = F.matrix.get(i, j);
      if (literal == 0) {
        continue; // Variable j does not occur in clause i
      }
      processed_v++;

      if (a.arr[j] == 0) {
        could_be_satisfiable = true;
        continue;
      }

      if (literal * a.arr[j] == 1) {
        clauseSatisfied =
            true; // Positive literal j is true or negative literal j is false
        c_remaining0--;
        l[i] = -1;
        break;
      }
    }

    if (!clauseSatisfied && !could_be_satisfiable) {
      return -1; // At least one clause is empty
    }

    nr_satisfied_clauses += clauseSatisfied;
  }

  if (nr_satisfied_clauses == c_remaining)
    return 1; // All clauses are satisfied
  c_remaining = c_remaining0;
  return 0;
}

int main(int argc, char *argv[]) {

  // Example formula : (A V B V !C) ^ (!A V !B V C)
  // All the satisfiable assignments:
  //  A !B C
  //  A !B !C
  //  A B C
  //  !A B C
  //  !A B !C
  //  !A !B C

  // START OF SECTION A

  // Matrix M(2, 3);
  // M[0][0] = 1;
  // M[0][1] = 1;
  // M[0][2] = -1;
  // M[1][0] = -1;
  // M[1][1] = -1;
  // M[1][2] = 1;

  // Formula F(M);

  // END OF SECTION A

  int c = std::stoi(argv[1]);
  int v = std::stoi(argv[2]);
  float d = std::stof(argv[3]);
  int seed = std::stoi(argv[4]);
  int t = std::stoi(argv[5]);

  // START OF SECTION B

  Formula F = generate_random_formula(c, v, d, seed);

  // END OF SECTION B

  std::cout << "F : \n";
  std::cout << F << '\n';

  std::deque<Assignment> global_stack; // global stack of partial assignments
  long long nr_of_satisfiable_assignments =
      0; // number of satidfiable assignmens from all threads

  Assignment assignment;
  assignment.arr = std::vector<int8_t>(F.v(), 0);
  global_stack.push_back(assignment); // initial empty assignment

  std::deque<Assignment> local_stack;
  bool finished = false;

  while (!finished) {
    if (local_stack.empty()) {

      if (global_stack.empty()) {
        finished = true;
        continue;
      }

      Assignment ass = global_stack.back();
      global_stack.pop_back();

      if (global_stack.empty() and ass.num_assigned != ass.size()) {
        std::vector<Assignment> new_as = generate_assignments(ass, t);
        std::move(new_as.begin(), new_as.end() - 1,
                  std::back_inserter(global_stack));
        local_stack.push_back(std::move(new_as[new_as.size() - 1]));
      } else {
        local_stack.push_back(std::move(ass));
      }
    }

    // assignment to be processed
    Assignment ass = local_stack.back();
    local_stack.pop_back();

    // Initialize l and c_remaining
    int c_remaining = F.c();
    std::vector<int> l = F.l;

    // execute under a base case is reached
    while (true) {

      // numer of remaining literals
      int n = F.v() - ass.num_assigned;
      int ans = evaluate(F, ass, l, c_remaining);

      // F is satisfiable under 'ass'
      if (ans == 1) {
        nr_of_satisfiable_assignments += (1 << n);
        break;
      }

      // F is unsatisfiable under 'ass'
      if (ans == -1) {
        break;
      }

      // F's satisfiability under 'ass' could not be determined
      if (ans == 0) {
        Assignment ass1 = ass;

        // add positive occurence of the next unassigned literal to 'ass'
        ass.arr[ass.num_assigned++] = 1;

        // add negative occurence of the next unassigned literal to a copy of
        // 'ass'
        ass1.arr[ass1.num_assigned++] = -1;

        // push the copy to the local stack
        local_stack.push_back(ass1);
      }
    }
  }

  std::cout << nr_of_satisfiable_assignments << "\n";
