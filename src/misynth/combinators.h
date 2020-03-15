#ifndef COMBINATORS_H
#define COMBINATORS_H

#include "util/vector.h"

class generator_permutation_with_repetitions
{
        // URL: https://rosettacode.org/wiki/Permutations_with_repetitions#C.2B.2B
    public:
        generator_permutation_with_repetitions(int s, int v)
            : m_slots(s),
              m_values(v),
              m_a(s)
        {
            reset();
        }



        bool do_next()
        {
            for (;;)
            {
                if (m_a[m_next_ind - 1] == m_values)
                {
                    m_next_ind--;
                    if (m_next_ind == 0)
                        return false;
                }
                else
                {
                    m_a[m_next_ind - 1]++;
                    while (m_next_ind < m_slots)
                    {
                        m_next_ind++;
                        m_a[m_next_ind - 1] = 1;
                    }

                    return true;
                }
            }
        }

        vector<unsigned int> &get_next()
        {
            return m_a;
        }
        void reset()
        {
            for (unsigned int i = 0; i < m_slots - 1; i++)
            {
                m_a[i] = 1;
            }
            m_a[m_slots - 1] = 0;

            m_next_ind = m_slots;
        }
        void do_print()
        {
            printf("(");
            for (int i = 0; i < m_slots; i++)
            {
                printf("%d", m_a[i]);
            }
            printf(")");
        }

    private:
        int m_slots;
        int m_values;
        int m_next_ind;
        vector<unsigned int> m_a;

};


class generator_combination_with_repetiton
{

    public:
        generator_combination_with_repetiton(unsigned int s, unsigned int v)
            : m_slots(s),
              m_values(v),
              m_v(s),
              m_is_first(true)
        {
            //reset();
        }



        bool do_next()
        {
            if (!m_is_first)
            {
                if (m_v.size() == 0)
                    return false;
                m_v[0] += 1;
            }
            else
            {
                m_is_first = false;
                return true;
            }
            for (unsigned int i = 0; i < m_slots; ++i)                 //vai um
            {
                if (m_v[i] + 1 > m_values)//if (m_v[i] > (m_values - 1))
                {
                    if (i + 1 >= m_slots)
                        return false;
                    m_v[i + 1] += 1;
                    for (int k = i; k >= 0; --k)
                    {
                        m_v[k] = m_v[i + 1];
                    }

                }
            }


            return true;
        }

        vector<unsigned int> &get_next()
        {
            return m_v;
        }
        void reset()
        {
            m_v.resize(m_slots, 0);
        }
        void do_print()
        {
            printf("(");
            for (unsigned int i = 0; i < m_slots; i++)
            {
                printf("%d", m_v[i]);
            }
            printf(")");
        }

    private:
        unsigned int m_slots;
        unsigned int m_values;
        vector<unsigned int> m_v;
        bool m_is_first;

};


template<class T>
void print_vector(const vector<T> &v)
{
    for (size_t i = 0; i < v.size(); ++i)
        printf("%d", v[i]);
    printf("\n");
}

#endif // COMBINATORS_H
