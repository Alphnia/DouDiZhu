#include <iostream>
#include <set>
#include <string>
#include <cassert>
#include <cstring> // 注意memset是cstring里的
#include <algorithm>
#include <functional>
#include <cmath>
#include <ctime>
#include <unordered_map>
#include <unordered_set>
#include "../jsoncpp/json.h" // 在平台上，C++编译时默认包含此库// 在平台上，C++编译时默认包含此库
#define SIMULATING_THRESHOLD 100
using namespace std;
#define rep(i,a,b) for(int i=(a);i<=(b);++i)
using std::set;
using std::sort;
using std::string;
using std::unique;
using std::pair;
using std::vector;
using std::hash;
using std::unordered_map;
using std::unordered_set;

constexpr int PLAYER_COUNT = 3;

const double C=1.414;

enum class Stage
{
    BIDDING, // 叫分阶段
    PLAYING     // 打牌阶段
};

enum class CardComboType
{
    PASS,        // 过
    SINGLE,        // 单张
    PAIR,        // 对子
    STRAIGHT,    // 顺子
    STRAIGHT2,    // 双顺
    TRIPLET,    // 三条
    TRIPLET1,    // 三带一
    TRIPLET2,    // 三带二
    BOMB,        // 炸弹
    QUADRUPLE2, // 四带二（只）
    QUADRUPLE4, // 四带二（对）
    PLANE,        // 飞机
    PLANE1,        // 飞机带小翼
    PLANE2,        // 飞机带大翼
    SSHUTTLE,    // 航天飞机
    SSHUTTLE2,    // 航天飞机带小翼
    SSHUTTLE4,    // 航天飞机带大翼
    ROCKET,        // 火箭
    INVALID        // 非法牌型
};

int cardComboScores[] = {
    0,    // 过
    1,    // 单张
    2,    // 对子
    6,    // 顺子
    6,    // 双顺
    4,    // 三条
    4,    // 三带一
    4,    // 三带二
    10, // 炸弹
    8,    // 四带二（只）
    8,    // 四带二（对）
    8,    // 飞机
    8,    // 飞机带小翼
    8,    // 飞机带大翼
    10, // 航天飞机（需要特判：二连为10分，多连为20分）
    10, // 航天飞机带小翼
    10, // 航天飞机带大翼
    16, // 火箭
    0    // 非法牌型
};

#ifndef _BOTZONE_ONLINE
string cardComboStrings[] = {
    "PASS",
    "SINGLE",
    "PAIR",
    "STRAIGHT",
    "STRAIGHT2",
    "TRIPLET",
    "TRIPLET1",
    "TRIPLET2",
    "BOMB",
    "QUADRUPLE2",
    "QUADRUPLE4",
    "PLANE",
    "PLANE1",
    "PLANE2",
    "SSHUTTLE",
    "SSHUTTLE2",
    "SSHUTTLE4",
    "ROCKET",
    "INVALID"};
#endif

// 用0~53这54个整数表示唯一的一张牌
using Card = short;
constexpr Card card_joker = 52;
constexpr Card card_JOKER = 53;

// 除了用0~53这54个整数表示唯一的牌，
// 这里还用另一种序号表示牌的大小（不管花色），以便比较，称作等级（Level）
// 对应关系如下：
// 3 4 5 6 7 8 9 10    J Q K    A    2    小王    大王
// 0 1 2 3 4 5 6 7    8 9 10    11    12    13    14
using Level = short;
constexpr Level MAX_LEVEL = 15;
constexpr Level MAX_STRAIGHT_LEVEL = 11;
constexpr Level level_joker = 13;
constexpr Level level_JOKER = 14;



/* 状态 */

// 我的牌有哪些
set<Card> myCards;

// 地主明示的牌有哪些
unordered_set<Card> landlordPublicCards;

//哪些牌不能确定位置
set<Card> uncertainCards;
vector<Card> uncertainCardsList;

//地主还没打出的地主牌
unordered_set<Card> landlordUnplayedCards;

// 大家从最开始到现在都出过什么
vector<vector<Card>> whatTheyPlayed[PLAYER_COUNT];



// 大家还剩多少牌
short cardRemaining[PLAYER_COUNT] = {17, 17, 17};

// 我是几号玩家（0-地主，1-农民甲，2-农民乙）
int myPosition;

// 地主位置
int landlordPosition = -1;

// 地主叫分
int landlordBid = -1;

// 阶段
Stage stage = Stage::BIDDING;

// 自己的第一回合收到的叫分决策
vector<int> bidInput;


/**
 * 将Card变成Level
 */
constexpr Level card2level(Card card)
{
    return card / 4 + card / 53;
}



// 牌的组合，用于计算牌型

struct CardCombo
{
    // 表示同等级的牌有多少张
    // 会按个数从大到小、等级从大到小排序
    struct CardPack
    {
        Level level;
        short count;

        bool operator<(const CardPack& b) const
        {
            if (count == b.count)
                return level > b.level;
            return count > b.count;
        }
    };
    vector<Card> cards;         // 原始的牌，未排序
    vector<CardPack> packs;     // 按数目和大小排序的牌种
    CardComboType comboType; // 算出的牌型
    Level comboLevel = 0;     // 算出的大小序
    static bool divided ;//牌型是否被拆分过
    int valueofdeck;//牌型估值
    vector<CardCombo>option;
    /**
                          * 检查个数最多的CardPack递减了几个
                          */
    int findMaxSeq() const
    {
        for (unsigned c = 1; c < packs.size(); c++)
            if (packs[c].count != packs[0].count ||
                packs[c].level != packs[c - 1].level - 1)
                return c;
        return packs.size();
    }

    /**
    * 这个牌型最后算总分的时候的权重
    */
    int getWeight() const
    {
        if (comboType == CardComboType::SSHUTTLE ||
            comboType == CardComboType::SSHUTTLE2 ||
            comboType == CardComboType::SSHUTTLE4)
            return cardComboScores[(int)comboType] + (findMaxSeq() > 2) * 10;
        return cardComboScores[(int)comboType];
    }

    // 创建一个空牌组
    CardCombo() : comboType(CardComboType::PASS) {}

    /**
    * 通过Card（即short）类型的迭代器创建一个牌型
    * 并计算出牌型和大小序等
    * 假设输入没有重复数字（即重复的Card）
    */
    template <typename CARD_ITERATOR>
    CardCombo(CARD_ITERATOR begin, CARD_ITERATOR end)
    {
        // 特判：空
        if (begin == end)
        {
            comboType = CardComboType::PASS;
            return;
        }

        // 每种牌有多少个
        short counts[MAX_LEVEL + 1] = {};

        // 同种牌的张数（有多少个单张、对子、三条、四条）
        short countOfCount[5] = {};

        cards = vector<Card>(begin, end);
        for (Card c : cards)
            counts[card2level(c)]++;
        for (Level l = 0; l <= MAX_LEVEL; l++)
            if (counts[l])
            {
                packs.push_back(CardPack{ l, counts[l] });
                countOfCount[counts[l]]++;
            }
        sort(packs.begin(), packs.end());

        // 用最多的那种牌总是可以比较大小的
        comboLevel = packs[0].level;

        // 计算牌型
        // 按照 同种牌的张数 有几种 进行分类
        vector<int> kindOfCountOfCount;
        for (int i = 0; i <= 4; i++)
            if (countOfCount[i])
                kindOfCountOfCount.push_back(i);
        sort(kindOfCountOfCount.begin(), kindOfCountOfCount.end());

        int curr, lesser;

        switch (kindOfCountOfCount.size())
        {
        case 1: // 只有一类牌
            curr = countOfCount[kindOfCountOfCount[0]];
            switch (kindOfCountOfCount[0])
            {
            case 1:
                // 只有若干单张
                if (curr == 1)
                {
                    comboType = CardComboType::SINGLE;
                    return;
                }
                if (curr == 2 && packs[1].level == level_joker)
                {
                    comboType = CardComboType::ROCKET;
                    return;
                }
                if (curr >= 5 && findMaxSeq() == curr &&
                    packs.begin()->level <= MAX_STRAIGHT_LEVEL)
                {
                    comboType = CardComboType::STRAIGHT;
                    return;
                }
                break;
            case 2:
                // 只有若干对子
                if (curr == 1)
                {
                    comboType = CardComboType::PAIR;
                    return;
                }
                if (curr >= 3 && findMaxSeq() == curr &&
                    packs.begin()->level <= MAX_STRAIGHT_LEVEL)
                {
                    comboType = CardComboType::STRAIGHT2;
                    return;
                }
                break;
            case 3:
                // 只有若干三条
                if (curr == 1)
                {
                    comboType = CardComboType::TRIPLET;
                    return;
                }
                if (findMaxSeq() == curr &&
                    packs.begin()->level <= MAX_STRAIGHT_LEVEL)
                {
                    comboType = CardComboType::PLANE;
                    return;
                }
                break;
            case 4:
                // 只有若干四条
                if (curr == 1)
                {
                    comboType = CardComboType::BOMB;
                    return;
                }
                if (findMaxSeq() == curr &&
                    packs.begin()->level <= MAX_STRAIGHT_LEVEL)
                {
                    comboType = CardComboType::SSHUTTLE;
                    return;
                }
            }
            break;
        case 2: // 有两类牌
            curr = countOfCount[kindOfCountOfCount[1]];
            lesser = countOfCount[kindOfCountOfCount[0]];
            if (kindOfCountOfCount[1] == 3)
            {
                // 三条带？
                if (kindOfCountOfCount[0] == 1)
                {
                    // 三带一
                    if (curr == 1 && lesser == 1)
                    {
                        comboType = CardComboType::TRIPLET1;
                        return;
                    }
                    if (findMaxSeq() == curr && lesser == curr &&
                        packs.begin()->level <= MAX_STRAIGHT_LEVEL)
                    {
                        comboType = CardComboType::PLANE1;
                        return;
                    }
                }
                if (kindOfCountOfCount[0] == 2)
                {
                    // 三带二
                    if (curr == 1 && lesser == 1)
                    {
                        comboType = CardComboType::TRIPLET2;
                        return;
                    }
                    if (findMaxSeq() == curr && lesser == curr &&
                        packs.begin()->level <= MAX_STRAIGHT_LEVEL)
                    {
                        comboType = CardComboType::PLANE2;
                        return;
                    }
                }
            }
            if (kindOfCountOfCount[1] == 4)
            {
                // 四条带？
                if (kindOfCountOfCount[0] == 1)
                {
                    // 四条带两只 * n
                    if (curr == 1 && lesser == 2)
                    {
                        comboType = CardComboType::QUADRUPLE2;
                        return;
                    }
                    if (findMaxSeq() == curr && lesser == curr * 2 &&
                        packs.begin()->level <= MAX_STRAIGHT_LEVEL)
                    {
                        comboType = CardComboType::SSHUTTLE2;
                        return;
                    }
                }
                if (kindOfCountOfCount[0] == 2)
                {
                    // 四条带两对 * n
                    if (curr == 1 && lesser == 2)
                    {
                        comboType = CardComboType::QUADRUPLE4;
                        return;
                    }
                    if (findMaxSeq() == curr && lesser == curr * 2 &&
                        packs.begin()->level <= MAX_STRAIGHT_LEVEL)
                    {
                        comboType = CardComboType::SSHUTTLE4;
                        return;
                    }
                }
            }
        }

        comboType = CardComboType::INVALID;
    }

    /**
    * 判断指定牌组能否大过当前牌组（这个函数不考虑过牌的情况！）
    */
    bool canBeBeatenBy(const CardCombo& b) const
    {
        if (comboType == CardComboType::INVALID || b.comboType == CardComboType::INVALID)
            return false;
        if (b.comboType == CardComboType::ROCKET)
            return true;
        if (b.comboType == CardComboType::BOMB)
            switch (comboType)
            {
            case CardComboType::ROCKET:
                return false;
            case CardComboType::BOMB:
                return b.comboLevel > comboLevel;
            default:
                return true;
            }
        return b.comboType == comboType && b.cards.size() == cards.size() && b.comboLevel > comboLevel;
    }
    //手牌拆分函数
    template <typename CARD_ITERATOR>
    static void divide(vector<CardCombo>& option, CARD_ITERATOR begin, CARD_ITERATOR end)
    {
        short counts[MAX_LEVEL + 1] = {};
        divided = true;
        auto deck = vector<Card>(begin, end); // 手牌
        int numOfMyCard = deck.size();
        unsigned short kindCount = 0;
        // 先数一下手牌里每种牌有多少个
        for (Card c : deck)
        {
            counts[card2level(c)]++;
        }
        //PASS走法
        option.push_back(CardCombo());
        //单张走法
        for (int i = 0; i < MAX_LEVEL; ++i)
        {
            vector<Card> tmp;
            if (counts[i] >= 1)
            {
                bool flag = 0;
                for (int p = 0; p < 4; ++p)
                {
                    for (Card c : deck)
                    {
                        if (c == p + i * 4)
                        {
                            tmp.push_back(c);
                            flag = 1;
                            break;
                        }
                    }
                    if (flag == 1)
                        break;
                }
                option.push_back(CardCombo(tmp.begin(), tmp.end()));
            }
        }
        //对子走法
        for (int i = 0; i < MAX_LEVEL; ++i)
        {
            vector<Card> tmp;
            if (counts[i] >= 2)
            {
                int p = 0;
                for (p; p < 4; ++p)
                {
                    int count = 0;
                    for (Card c : deck)
                    {
                        if (c == p + i * 4)
                        {
                            tmp.push_back(c);
                            count++;
                            break;
                        }
                    }
                    if (count == 2)
                        break;
                }
            }
            option.push_back(CardCombo(tmp.begin(), tmp.end()));
        }
        //顺子走法
        for (int i = 5; i < 13; ++i)//顺子长度
        {
            for (int j = 0; j < 8; ++j)
            {
                vector<Card> tmp;
                if (counts[j])
                {
                    int k;
                    for (k = 0; k < i; ++k)
                    {
                        if (!counts[j + k])
                            break;
                        bool flag = 0;
                        for (int p = 0; p < 4; ++p)
                        {
                            for (Card c : deck)
                            {
                                if (c == p + (j + k) * 4)
                                {
                                    tmp.push_back(c);
                                    flag = 1;
                                    break;
                                }
                            }
                            if (flag == 1)
                                break;
                        }
                    }
                    if (k == i)
                        option.push_back(CardCombo(tmp.begin(), tmp.end()));
                }
            }
        }
        //双顺走法
        for (int i = 5; i < 11; ++i)//顺子长度
        {
            for (int j = 0; j < 8; ++j)
            {
                vector<Card> tmp;
                if (counts[j] >= 2)
                {
                    int k;
                    for (k = 0; k < i; ++k)
                    {
                        if (counts[j + k] < 2)
                            break;
                        int p = 0;
                        for (p; p < 4; ++p)
                        {
                            int count = 0;
                            for (Card c : deck)
                            {
                                if (c == p + (j + k) * 4)
                                {
                                    tmp.push_back(c);
                                    count++;
                                    break;
                                }
                            }
                            if (count == 2)
                                break;
                        }
                    }
                    if (k == i)
                        option.push_back(CardCombo(tmp.begin(), tmp.end()));
                }
            }
        }
        //三条走法
        for (int i = 0; i < MAX_LEVEL; ++i)
        {
            vector<Card> tmp;
            if (counts[i] >= 3)
            {
                int p = 0;
                for (p; p < 4; ++p)
                {
                    int count = 0;
                    for (Card c : deck)
                    {
                        if (c == p + i * 4)
                        {
                            tmp.push_back(c);
                            count++;
                            break;
                        }
                    }
                    if (count == 3)
                        break;
                }
            }
            option.push_back(CardCombo(tmp.begin(), tmp.end()));
            //三带一
            for (int q = 0; q < MAX_LEVEL; ++q)
            {
                vector<Card> tmp;
                if (q == i)
                    continue;
                if (counts[q])
                {
                    bool flag = 0;
                    for (int p = 0; p < 4; ++p)
                    {
                        for (Card c : deck)
                        {
                            if (c == p + q * 4)
                            {
                                tmp.push_back(c);
                                flag = 1;
                                break;
                            }
                        }
                        if (flag == 1)
                            break;
                    }
                    option.push_back(CardCombo(tmp.begin(), tmp.end()));
                    tmp.pop_back();
                }
            }
            //三带对
            for (int q = 0; q < MAX_LEVEL; ++q)
            {
                vector<Card> tmp;
                if (q == i)
                    continue;
                if (counts[q] >= 2)
                {
                    int count = 0;
                    for (int p = 0; p < 4; ++p)
                    {
                        for (Card c : deck)
                        {
                            if (c == p + q * 4)
                            {
                                tmp.push_back(c);
                                count++;
                                break;
                            }
                        }
                        if (count == 2)
                            break;
                    }
                    option.push_back(CardCombo(tmp.begin(), tmp.end()));
                    tmp.pop_back();
                    tmp.pop_back();
                }
            }
        }
        //炸弹走法
        for (int i = 0; i < MAX_LEVEL; ++i)
        {
            vector<Card> tmp;
            if (counts[i] > 3)
            {
                int p = 0;
                for (p; p < 4; ++p)
                {
                    tmp.push_back(p + i * 4);
                }
                option.push_back(CardCombo(tmp.begin(), tmp.end()));
                //四带两只
                vector<Card> temp;
                for (int q = 0; q < MAX_LEVEL; ++q)
                {
                    if (q == i)
                        continue;
                    if (counts[q])
                    {
                        bool flag = 0;
                        for (int p = 0; p < 4; ++p)
                        {
                            for (Card c : deck)
                            {
                                if (c == p + q * 4)
                                {
                                    temp.push_back(c);
                                    flag = 1;
                                    break;
                                }
                            }
                            if (flag == 1)
                                break;
                        }
                    }
                }
                for (vector<Card>::iterator i = temp.begin(); i != temp.end(); ++i)
                {
                    for (vector<Card>::iterator j = i + 1; j != temp.end(); ++j)
                    {
                        tmp.push_back(*i);
                        tmp.push_back(*j);
                        option.push_back(CardCombo(tmp.begin(), tmp.end()));
                        tmp.pop_back();
                        tmp.pop_back();
                    }
                }
                //四带两对
                vector<CardCombo> temp2;
                for (int q = 0; q < MAX_LEVEL; ++q)
                {
                    vector<Card> temptemp;
                    if (q == i)
                        continue;
                    if (counts[q] >= 2)
                    {
                        bool flag = 0;
                        int count = 0;
                        for (int p = 0; p < 4; ++p)
                        {
                            for (Card c : deck)
                            {
                                if (c == p + q * 4)
                                {
                                    count++;
                                    temptemp.push_back(c);
                                    break;
                                }
                            }
                            if (count == 2)
                            {
                                temp2.push_back(CardCombo(temptemp.begin(), temptemp.end()));
                                break;
                            }
                        }
                    }
                }
                for (auto i = temp2.begin(); i != temp2.end(); ++i)
                {
                    for (auto j = i + 1; j != temp2.end(); ++j)
                    {
                        tmp.push_back((*i).cards[0]);
                        tmp.push_back((*i).cards[1]);
                        tmp.push_back((*j).cards[0]);
                        tmp.push_back((*j).cards[0]);
                        option.push_back(CardCombo(tmp.begin(), tmp.end()));
                        tmp.pop_back();
                        tmp.pop_back();
                        tmp.pop_back();
                        tmp.pop_back();
                    }
                }
            }
        }
        //火箭
        if (counts[card_joker] && counts[card_JOKER])
        {
            vector<Card> tmp;
            tmp.push_back(card_joker);
            tmp.push_back(card_JOKER);
            option.push_back(CardCombo(tmp.begin(), tmp.end()));
        }
        //飞机
        for (int i = 0; i < MAX_LEVEL; ++i)
        {
            vector<Card> tmp;
            if (counts[i] >= 3 && counts[i + 1] >= 3)
            {
                int p = 0;
                for (; p < 4; ++p)
                {
                    int count = 0;
                    for (Card c : deck)
                    {
                        if (c == p + i * 4)
                        {
                            tmp.push_back(c);
                            count++;
                            break;
                        }
                    }
                    if (count == 3)
                        break;
                }
                for (p = 0; p < 4; ++p)
                {
                    int count = 0;
                    for (Card c : deck)
                    {
                        if (c == p + (i + 1) * 4)
                        {
                            tmp.push_back(c);
                            count++;
                            break;
                        }
                    }
                    if (count == 3)
                        break;
                }
                option.push_back(CardCombo(tmp.begin(), tmp.end()));
                //飞机带小翼
                vector<Card> temp;
                for (int q = 0; q < MAX_LEVEL; ++q)
                {
                    if (q == i || q == i + 1)
                        continue;
                    int cnt = 0;
                    if (counts[q])
                    {
                        bool flag = 0;
                        for (int p = 0; p < 4; ++p)
                        {
                            for (Card c : deck)
                            {
                                if (c == p + q * 4)
                                {
                                    temp.push_back(c);
                                    flag = 1;
                                    cnt++;
                                    break;
                                }
                            }
                            if (flag == 1)
                                break;

                        }
                    }
                }
                for (auto i = temp.begin(); i != temp.end(); ++i)
                {
                    for (auto j = i + 1; j != temp.end(); ++j)
                    {
                        tmp.push_back(*i);
                        tmp.push_back(*j);
                        option.push_back(CardCombo(tmp.begin(), tmp.end()));
                        tmp.pop_back();
                        tmp.pop_back();
                    }
                }
                //飞机带大翼
                vector<CardCombo> temp3;
                for (int q = 0; q < MAX_LEVEL; ++q)
                {
                    vector<Card> temptemp;
                    if (q == i || q == i + 1)
                        continue;
                    if (counts[q] >= 2)
                    {
                        bool flag = 0;
                        int count = 0;
                        for (int p = 0; p < 4; ++p)
                        {
                            count++;
                            for (Card c : deck)
                            {

                                if (c == p + q * 4)
                                {
                                    count++;
                                    temptemp.push_back(c);
                                    break;
                                }
                            }
                            if (count == 2)
                            {
                                temp3.push_back(CardCombo(temptemp.begin(),temptemp.end()));
                                break;
                            }
                        }
                    }
                }
                for (auto i = temp3.begin(); i != temp3.end(); ++i)
                {
                    for (auto j = i + 1; j != temp3.end(); ++j)
                    {
                        tmp.push_back((*i).cards[0]);
                        tmp.push_back((*i).cards[1]);
                        tmp.push_back((*j).cards[0]);
                        tmp.push_back((*j).cards[1]);
                        option.push_back(CardCombo(tmp.begin(), tmp.end()));
                        tmp.pop_back();
                        tmp.pop_back();
                        tmp.pop_back();
                        tmp.pop_back();
                    }
                }
                //飞机多于三个
                int t = i + 2;
                int d = 2;
                while (counts[t] >= 3)
                {
                    d++;
                    if (t == 12)
                        break;
                    int p = 0;
                    for (p; p < 4; ++p)
                    {
                        int count = 0;
                        for (Card c : deck)
                        {
                            if (c == p + t * 4)
                            {
                                tmp.push_back(c);
                                count++;
                                break;
                            }
                        }
                        if (count == 3)
                            break;
                    }
                    option.push_back(CardCombo(tmp.begin(), tmp.end()));
                }
                //飞机带小翼以及大翼多于三个怎么写！！！
            }
        }
        //航天飞机
        for (int i = 0; i < MAX_LEVEL; ++i)
        {
            vector<Card> tmp;
            if (counts[i] > 3 && counts[i + 1] > 3)
            {
                for (int p = 0; p < 4; ++p)
                {
                    tmp.push_back(p + i * 4);
                }
                for (int p = 0; p < 4; ++p)
                {
                    tmp.push_back(p + (i + 1) * 4);
                }
                option.push_back(CardCombo(tmp.begin(), tmp.end()));
                //航天飞机带小翼
                vector<Card> temp;
                for (int q = 0; q < MAX_LEVEL; ++q)
                {
                    if (q == i || q == i + 1)
                        continue;
                    if (counts[q])
                    {
                        bool flag = 0;
                        for (int p = 0; p < 4; ++p)
                        {
                            for (Card c : deck)
                            {
                                if (c == p + i * 4)
                                {
                                    temp.push_back(c);
                                    flag = 1;
                                    break;
                                }
                            }
                            if (flag == 1)
                                break;
                        }
                    }
                }
                for (vector<Card>::iterator i = temp.begin(); i != temp.end(); ++i)
                {
                    for (auto j = i + 1; j != temp.end(); ++j)
                    {
                        for (auto k = j + 1; k != temp.end(); ++k)
                        {
                            for (auto l = k + 1; l != temp.end(); ++l)
                            {
                                {
                                    tmp.push_back(*i);
                                    tmp.push_back(*j);
                                    tmp.push_back(*k);
                                    tmp.push_back(*l);
                                    option.push_back(CardCombo(tmp.begin(), tmp.end()));
                                    tmp.pop_back();
                                    tmp.pop_back();
                                    tmp.pop_back();
                                    tmp.pop_back();
                                }
                            }
                        }
                    }
                }
                //航天飞机带大翼，只能是两个炸弹 四个对子
                if (deck.size() == 20)
                {
                    int numOfDouble = 0;
                    for (int i = 0; i < MAX_LEVEL; ++i)
                    {
                        if (counts[i] == 2)
                            numOfDouble++;
                    }
                    if (numOfDouble == 4)
                    {
                        option.push_back(CardCombo(begin, end));
                    }
                }
                if (landlordPosition == myPosition && numOfMyCard >= 18)//才有可能出现三连的航天飞机
                {
                    for (int i = 0; i < MAX_LEVEL; ++i)
                    {
                        vector<Card> tmp;
                        if (counts[i] > 3 && counts[i + 1] > 3 && counts[i + 2] > 3)
                        {
                            for (int p = 0; p < 4; ++p)
                            {
                                tmp.push_back(p + i * 4);
                            }
                            for (int p = 0; p < 4; ++p)
                            {
                                tmp.push_back(p + (i + 1) * 4);
                            }
                            for (int p = 0; p < 4; ++p)
                            {
                                tmp.push_back(p + (i + 2) * 4);
                            }
                            option.push_back(CardCombo(tmp.begin(), tmp.end()));
                            if (numOfMyCard - 12 >= 6)
                            {
                                for (int q = 0; q < MAX_LEVEL; ++q)
                                {
                                    if (q == i || q == i + 1 || q == i + 2)
                                        continue;
                                    if (counts[q])
                                    {
                                        bool flag = 0;
                                        for (int p = 0; p < 4; ++p)
                                        {
                                            for (Card c : deck)
                                            {
                                                if (c == p + i * 4)
                                                {
                                                    temp.push_back(c);
                                                    flag = 1;
                                                    break;
                                                }
                                            }
                                            if (flag == 1)
                                                break;
                                        }
                                    }
                                }
                            }
                            if (temp.size() < 6)
                                break;
                            //航天飞机带小翼
                            for (vector<Card>::iterator i = temp.begin(); i != temp.end(); ++i)
                            {
                                for (auto j = i + 1; j != temp.end(); ++j)
                                {
                                    for (auto k = j + 1; k != temp.end(); ++k)
                                    {
                                        for (auto l = k + 1; l != temp.end(); ++l)
                                        {
                                            for (auto o = l + 1; o != temp.end(); ++o)
                                            {
                                                for (auto s = o + 1; s != temp.end(); ++s)
                                                {
                                                    tmp.push_back(*i);
                                                    tmp.push_back(*j);
                                                    tmp.push_back(*k);
                                                    tmp.push_back(*l);
                                                    tmp.push_back(*o);
                                                    tmp.push_back(*s);
                                                    option.push_back(CardCombo(tmp.begin(), tmp.end()));
                                                    tmp.pop_back();
                                                    tmp.pop_back();
                                                    tmp.pop_back();
                                                    tmp.pop_back();
                                                    tmp.pop_back();
                                                    tmp.pop_back();
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    template <typename CARD_ITERATOR>
    void findValid(CARD_ITERATOR begin, CARD_ITERATOR end)
    {
        if (comboType == CardComboType::PASS) // 如果不需要大过谁，只需要随便出,那么可出牌组即为所有可能情况，要进行手牌拆分，列举所有可能情况
        {
            if (!divided)
                divide(option, begin, end);
        }

        // 然后先看一下是不是火箭，是的话就过
        if (comboType == CardComboType::ROCKET)
            return;
        // 现在打算从手牌中凑出同牌型的牌
        auto deck = vector<Card>(begin, end); // 手牌
        short counts[MAX_LEVEL + 1] = {};

        unsigned short kindCount = 0;

        // 先数一下手牌里每种牌有多少个
        for (Card c : deck)
            counts[card2level(c)]++;

        // 手牌如果不够用，直接不用凑了，看看能不能炸吧
        if (deck.size() < cards.size())
            goto failure;

        // 再数一下手牌里有多少种牌
        for (short c : counts)
            if (c)
                kindCount++;

        // 否则不断增大当前牌组的主牌，看看能不能找到匹配的牌组
        {
            // 开始增大主牌
            int mainPackCount = findMaxSeq();
            bool isSequential =
                comboType == CardComboType::STRAIGHT ||
                comboType == CardComboType::STRAIGHT2 ||
                comboType == CardComboType::PLANE ||
                comboType == CardComboType::PLANE1 ||
                comboType == CardComboType::PLANE2 ||
                comboType == CardComboType::SSHUTTLE ||
                comboType == CardComboType::SSHUTTLE2 ||
                comboType == CardComboType::SSHUTTLE4;
            for (Level i = 1;; i++) // 增大多少
            {
                for (int j = 0; j < mainPackCount; j++)
                {
                    int level = packs[j].level + i;

                    // 各种连续牌型的主牌不能到2，非连续牌型的主牌不能到小王，单张的主牌不能超过大王
                    if ((comboType == CardComboType::SINGLE && level > MAX_LEVEL) ||
                        (isSequential && level > MAX_STRAIGHT_LEVEL) ||
                        (comboType != CardComboType::SINGLE && !isSequential && level >= level_joker))
                        goto failure;

                    // 如果手牌中这种牌不够，就不用继续增了
                    if (counts[level] < packs[j].count)
                        goto next;
                }

                {
                    // 找到了合适的主牌，那么从牌呢？
                    // 如果手牌的种类数不够，那从牌的种类数就不够，也不行
                    if (kindCount < packs.size())
                        continue;

                    // 好终于可以了
                    // 计算每种牌的要求数目吧
                    short requiredCounts[MAX_LEVEL + 1] = {};
                    for (int j = 0; j < mainPackCount; j++)
                        requiredCounts[packs[j].level + i] = packs[j].count;
                    for (unsigned j = mainPackCount; j < packs.size(); j++)
                    {
                        Level k;
                        for (k = 0; k <= MAX_LEVEL; k++)
                        {
                            if (requiredCounts[k] || counts[k] < packs[j].count)
                                continue;
                            requiredCounts[k] = packs[j].count;
                            break;
                        }
                        if (k == MAX_LEVEL + 1) // 如果是都不符合要求……就不行了
                            goto next;
                    }

                    // 开始产生解
                    vector<Card> solve;
                    for (Card c : deck)
                    {
                        Level level = card2level(c);
                        if (requiredCounts[level])
                        {
                            solve.push_back(c);
                            requiredCounts[level]--;
                        }
                    }
                    CardCombo tmp = CardCombo(solve.begin(), solve.end());
                    option.insert(option.end(), tmp);
                }
            next:; // 再增大
            }
        }
    failure:
        // 实在找不到啊
        // 最后看一下能不能炸吧

        for (Level i = 0; i < level_joker; i++)
        {
            if (counts[i] == 4 && (comboType != CardComboType::BOMB || i > packs[0].level)) // 如果对方是炸弹，能炸的过才行
            {
                // 还真可以啊……
                Card bomb[] = { Card(i * 4), Card(i * 4 + 1), Card(i * 4 + 2), Card(i * 4 + 3) };
                option.push_back(CardCombo(bomb, bomb + 4));
            }
        }
        // 有没有火箭？
        if (counts[level_joker] + counts[level_JOKER] == 2)
        {
            Card rocket[] = { card_joker, card_JOKER };
            option.push_back(CardCombo(rocket, rocket + 2));
        }

    }
    int getvalue()
    {
        int value = 0;
        if (!divided)
        {
            option.clear();
            divide(option, cards.begin(), cards.end());
        }
        //根据手牌拆分函数先将我方牌型进行评估
        for (vector<CardCombo>::iterator i = option.begin(); i != option.end(); ++i)
        {
            value += (*i).valueofdeck;
        }
        bool known[55] = {};
        for (vector<Card>::iterator i = cards.begin(); i != cards.end(); ++i)
        {
            known[(*i)] = 1;
        }
        for (int k = 0; k < 3; ++k)
        {
            for (vector<vector<Card>>::iterator i = whatTheyPlayed[0].begin(); i != whatTheyPlayed[k].end(); ++i)
            {
                for (vector<Card>::iterator j = (*i).begin(); j != (*i).end(); ++j)
                {
                    known[(*j)] = 1;
                }
            }
        }

        if (myPosition == landlordPosition)
        {
            vector<CardCombo> optionOfOp;
            vector<Card> another;
            for (int i = 0; i < 54; ++i)
            {
                if (known[i] == 0)
                {
                    another.push_back(i);
                }
            }
            divide(optionOfOp, another.begin(), another.end());
            //根据手牌拆分函数先将我方牌型进行评估
            for (vector<CardCombo>::iterator i = optionOfOp.begin(); i != optionOfOp.end(); ++i)
            {
                value -= (*i).valueofdeck;
            }
        }
        return value;
    }
    void debugPrint()
    {
#ifndef _BOTZONE_ONLINE
        std::cout << "【" << cardComboStrings[(int)comboType] << "共" << cards.size() << "张，大小序" << comboLevel << "】";
#endif
    }
};

// 当前要出的牌需要大过谁
CardCombo lastValidCombo;

//CARDCOMBO START

struct CARDCOMBO
{
    CardComboType comboType;
    Card info[8]; // (first second):  三带一: 三个的牌, 一个的牌; 顺子: 长度, 开始的牌; 对子和单张: first=牌
    CARDCOMBO(CardComboType t=CardComboType::PASS):comboType(t){
        for(int i=0;i<8;i++) info[i]=-1;
    }
    
};
//顺: 长度, 开始的牌
//三带一/二 三个的牌, 一/两个的牌
//飞机/航天飞机 长度, 开始的牌, 一堆带的牌


template <>
struct std::hash<CARDCOMBO>
{
    size_t operator()(const CARDCOMBO & k)const{
        size_t ret=0;
        for(int i=0;i<8;i++) ret^=hash<Card>()(k.info[i]);
        return ret;
    }
};

/*struct CARDCOMBO
{
    _cardCombo played;
};

template <>
struct std::hash<CARDCOMBO>
{
    size_t operator()(const CARDCOMBO & k) const
    {
        return hash<_cardCombo>()(k.played[0])^hash<_cardCombo>()(k.played[1])^hash<_cardCombo>()(k.played[2]);
    }
};
*/
CARDCOMBO change(const CardCombo && tmp)
{
    CARDCOMBO ret(tmp.comboType);
    switch (tmp.comboType) {
        case CardComboType::SINGLE:
        case CardComboType::PAIR:
        case CardComboType::TRIPLET:
        case CardComboType::BOMB:
            ret.info[0]=tmp.packs[0].level;
            break;
            
        case CardComboType::STRAIGHT:
        case CardComboType::STRAIGHT2:
        case CardComboType::PLANE:
        case CardComboType::SSHUTTLE:
            ret.info[0]=tmp.packs[0].level-(*(tmp.packs.end()-1)).level+1;
            ret.info[1]=(*(tmp.packs.end()-1)).level;
            break;
        
        case CardComboType::TRIPLET1:
        case CardComboType::TRIPLET2:
            ret.info[0]=tmp.packs[0].level;
            ret.info[1]=tmp.packs[1].level;
            
        case CardComboType::PASS:
        case CardComboType::ROCKET:
            break;
        
        case CardComboType::INVALID:
            throw "INVALID EDGE";
            
        default:
            int tot=0, t=tmp.packs[0].count, n=tmp.packs.size();
            bool flag=true;
            for(int i=1;i<n;i++)
                if(tmp.packs[i].count!=t)
                {
                    if(flag)
                    {
                        if(i!=1) ret.info[tot++]=i;
                        ret.info[tot++]=tmp.packs[i-1].level;
                        flag=false;
                    }
                    ret.info[tot++]=tmp.packs[i].level;
                }
    }
    return ret;
}
CARDCOMBO change(const CardCombo & tmp)
{
    return change(move(tmp));
}


//CARDCOMBO END


struct NODE //不用存牌型信息因为可以从之前的出牌信息中推断
{
    int visitTime = 0;
    int value=0;
    NODE *father = NULL;
    unordered_map<CARDCOMBO, NODE *> son;
    vector<Card> pai;

    NODE(){}
    NODE(NODE *y):father(y){}
    NODE(const vector<Card> & p):pai(p){}
    NODE(const set<Card> & p):pai(p.begin(), p.end()){}
    template <class IT>
    NODE(const IT & p1, const IT & p2):pai(p1, p2){}

    double formula(NODE *now_son){
        return (double)now_son->value/(now_son->visitTime+1)+C*sqrt(log((double)visitTime)/(now_son->visitTime+1));
    }
    pair<CARDCOMBO, NODE *> choose(){
        NODE *d=NULL;
        pair<CARDCOMBO, NODE *> ans;
        double mx=0,tmp=0;

        for(auto i=son.begin();i!=son.end();i++){
            d=i->second;
            tmp=formula(d);
            if(tmp>mx)
            {
                mx=tmp;
                ans=*i;
            }
        }
        return ans;
    }
};

namespace BotzoneIO
{
using namespace std;
void read()
{
    // 读入输入（平台上的输入是单行）
    string line;
    getline(cin, line);
    Json::Value input;
    Json::Reader reader;
    reader.parse(line, input);
    
    for(int i=0;i<54;i++) uncertainCards.insert(i);
    
    // 首先处理第一回合，得知自己是谁、有哪些牌
    {
        auto firstRequest = input["requests"][0u]; // 下标需要是 unsigned，可以通过在数字后面加u来做到
        auto own = firstRequest["own"];
        for (unsigned i = 0; i < own.size(); i++)
        {
            myCards.insert(own[i].asInt());
            
            uncertainCards.erase(own[i].asInt());
            
        }
        if (!firstRequest["bid"].isNull())
        {
            // 如果还可以叫分，则记录叫分
            auto bidHistory = firstRequest["bid"];
            myPosition = bidHistory.size();
            for (unsigned i = 0; i < bidHistory.size(); i++)
                bidInput.push_back(bidHistory[i].asInt());
        }
    }
    
    // history里第一项（上上家）和第二项（上家）分别是谁的决策
    int whoInHistory[] = {(myPosition - 2 + PLAYER_COUNT) % PLAYER_COUNT, (myPosition - 1 + PLAYER_COUNT) % PLAYER_COUNT};
    
    int turn = input["requests"].size();
    for (int i = 0; i < turn; i++)
    {
        auto request = input["requests"][i];
        auto llpublic = request["publiccard"];
        if (!llpublic.isNull())
        {
            // 第一次得知公共牌、地主叫分和地主是谁
            landlordPosition = request["landlord"].asInt();
            landlordBid = request["finalbid"].asInt();
            myPosition = request["pos"].asInt();
            whoInHistory[0] = (myPosition - 2 + PLAYER_COUNT) % PLAYER_COUNT;
            whoInHistory[1] = (myPosition - 1 + PLAYER_COUNT) % PLAYER_COUNT;
            cardRemaining[landlordPosition] += llpublic.size();
            for (unsigned i = 0; i < llpublic.size(); i++)
            {
                landlordPublicCards.insert(llpublic[i].asInt());
                
                landlordUnplayedCards.insert(llpublic[i].asInt());
                uncertainCards.erase(llpublic[i].asInt());
                
                if (landlordPosition == myPosition)
                    myCards.insert(llpublic[i].asInt());
            }
        }
        
        auto history = request["history"]; // 每个历史中有上家和上上家出的牌
        if (history.isNull())
            continue;
        stage = Stage::PLAYING;
        
        // 逐次恢复局面到当前
        int howManyPass = 0;
        for (int p = 0; p < 2; p++)
        {
            int player = whoInHistory[p];    // 是谁出的牌
            auto playerAction = history[p]; // 出的哪些牌
            vector<Card> playedCards;
            for (unsigned _ = 0; _ < playerAction.size(); _++) // 循环枚举这个人出的所有牌
            {
                int card = playerAction[_].asInt(); // 这里是出的一张牌
                playedCards.push_back(card);
                
                if(player==landlordPosition&&landlordUnplayedCards.count(card))
                    landlordUnplayedCards.erase(card);
                else if(uncertainCards.count(card))
                    uncertainCards.erase(card);
            }
            whatTheyPlayed[player].push_back(playedCards); // 记录这段历史
            cardRemaining[player] -= playerAction.size();
            
            if (playerAction.size() == 0)
                howManyPass++;
            else
                lastValidCombo = CardCombo(playedCards.begin(), playedCards.end());
        }
        
        if (howManyPass == 2)
            lastValidCombo = CardCombo();
        
        if (i < turn - 1)
        {
            // 还要恢复自己曾经出过的牌
            auto playerAction = input["responses"][i]; // 出的哪些牌
            vector<Card> playedCards;
            for (unsigned _ = 0; _ < playerAction.size(); _++) // 循环枚举自己出的所有牌
            {
                int card = playerAction[_].asInt(); // 这里是自己出的一张牌
                myCards.erase(card);                // 从自己手牌中删掉
                playedCards.push_back(card);
            }
            whatTheyPlayed[myPosition].push_back(playedCards); // 记录这段历史
            cardRemaining[myPosition] -= playerAction.size();
        }
    }
    for(Card card: uncertainCards)
        uncertainCardsList.push_back(card);
}

/**
 * 输出叫分（0, 1, 2, 3 四种之一）
 */
void bid(int value)
{
    Json::Value result;
    result["response"] = value;
    
    Json::FastWriter writer;
    cout << writer.write(result) << endl;
}

/**
 * 输出打牌决策，begin是迭代器起点，end是迭代器终点
 * CARD_ITERATOR是Card（即short）类型的迭代器
 */
template <typename CARD_ITERATOR>
void play(CARD_ITERATOR begin, CARD_ITERATOR end)
{
    Json::Value result, response(Json::arrayValue);
    for (; begin != end; begin++)
        response.append(*begin);
    result["response"] = response;
    
    Json::FastWriter writer;
    cout << writer.write(result) << endl;
}
}

class Decider
{
public:
    virtual CARDCOMBO decide() = 0;
};

class MCTS : public Decider
{
public:
    NODE *root[3]{NULL, NULL, NULL};//root0是自己，其他按顺序顺延
    NODE *now[3]{NULL, NULL, NULL};//select出来的三个节点存在这里，就不用return三个NODE*了。。。
    void simulate();//每一次拓展节点的迭代大函数(在里头确定determination)
    void select(CardCombo );//选择一个还未被拓展完全的节点或者一个终局节点
    void expand(int, CardCombo);//扩展
    void backpropagate(NODE *,int );//更新value
    int random_play(int k, CardCombo Last);
    int reward();//计算某个非终局局面的收益
    CARDCOMBO bestStrategy();
    CARDCOMBO decide()
    {
        for (int i = 0; i < SIMULATING_THRESHOLD; i++)
            simulate();
        return bestStrategy();
    }
};
//0是地主1是农民甲2是农民乙
//3棵树

#define t_id(x) ((x-myPosition+3)%3)
//
void MCTS::simulate(){
    //确定好determination，初始化3个mcts的根节点。
    short _cardRemaining[3];
    for(int i=0;i<3;i++)
        _cardRemaining[i]=cardRemaining[(i+myPosition)%3]-(landlordPosition==(i+myPosition)%3?landlordUnplayedCards.size():0);
    shuffle(uncertainCardsList.begin(), uncertainCardsList.end(), rand);
    root[0]=new NODE(myCards);
    root[1]=new NODE(uncertainCardsList.begin(), uncertainCardsList.begin()+_cardRemaining[1]);
    root[2]=new NODE(uncertainCardsList.begin(), uncertainCardsList.begin()+_cardRemaining[2]);
    if(t_id(landlordPosition))
        for(Card card: landlordUnplayedCards)
            root[t_id(landlordPosition)]->pai.push_back(card);
    select(lastValidCombo);
    //CardCombo::divided=false; 这句加了之后编译不过
}
CARDCOMBO MCTS::bestStrategy(){
    return (root[0]->choose()).first;
}
int MCTS::reward(){

}
int MCTS::random_play(int k,CardCombo Last){

}

void MCTS::backpropagate(NODE *x,int val){
    if(x->father==NULL)return;
    NODE *y=x->father;
    y->value+=val;
    y->visitTime++;
    backpropagate(y,val);
}
void MCTS::expand(int who,CardCombo edge){
    int k;
    now[who]->son.insert(make_pair(change(edge),new NODE(now[who])));
    //son的牌是now[who]的牌减去edge；还得写个函数
    now[who]=now[who]->son.find(change(edge))->second;
    vector<CardCombo> opt[3];
    bool flag=0;
    const CardCombo emp;
    rep(j,1,2){
        k=(who+j)%3;
        CardCombo::divide(opt[k],now[k]->pai.begin(),now[k]->pai.end());
        for(auto i=opt[k].begin();i!=opt[k].end();i++){
            if(i->comboType==edge.comboType||edge.comboType==CardComboType::PASS){
                if(now[k]->son.find(change(*i))!=now[k]->son.end()){
                    continue;
                }
                else {
                    now[k]->son.insert(make_pair(change(*i), new NODE(now[k])));
                    //son的牌是now[who]的牌减去edge；同上
                    now[k]=now[k]->son.find(change(*i))->second;
                    edge=*i;
                    flag=1;
                    break;
                }
            }
        }
        if(!flag)edge=emp;//如果其中一家没有可以拓展的就先设置成pass然后尝试拓展下一家。
    }
    int val=random_play(who,edge);//返回的应该是对于树0，也就是玩家自己来说的，正为赢分，负为输分，算上加倍。
    
    backpropagate(now[0],val);
    if(myPosition==0)
    backpropagate(now[1],-val/2),backpropagate(now[2],-val/2);
    if(myPosition==1)
    backpropagate(now[1],val),backpropagate(now[2],-2*val);
    if(myPosition==2)
    backpropagate(now[1],-2*val),backpropagate(now[2],val);
}

void MCTS::select(CardCombo Last){
    vector<CardCombo> opt[3];
    rep(i,0,2)now[i]=root[i];
    int mx=0,tmp;
    CardCombo choice;
    while(!now[0]->pai.empty()&&!now[1]->pai.empty()&&!now[2]->pai.empty()){
        rep(k,0,2){
            CardCombo::divide(opt[k],now[k]->pai.begin(),now[k]->pai.end());
            for(auto i=opt[k].begin();i!=opt[k].end();i++){
                if((*i).comboType==Last.comboType||Last.comboType==CardComboType::PASS){
                    if(now[k]->son.find(change(*i))!=now[k]->son.end()){
                        tmp=now[k]->formula(now[k]->son.find(change(*i))->second);
                        if(mx<tmp){
                            mx=tmp;
                            choice=*i;
                        }
                    }
                    else {
                        expand(k,*i);
                        return;
                    }
                }
            }
            now[k]=now[k]->son.find(change(choice))->second;
            Last=choice;
        }
    }
}





class Rule : public Decider
{
public:
    CARDCOMBO decide();
};

int bidding(){
    auto maxBidIt = std::max_element(bidInput.begin(), bidInput.end());
    int maxBid = maxBidIt == bidInput.end() ? -1 : *maxBidIt;
    int bidValue = rand() % (3 - maxBid) + maxBid + 1;
    return bidValue;
}

int main()
{
    srand((unsigned int)time(nullptr));
    BotzoneIO::read();
    
    if (stage == Stage::BIDDING)
    {
        // 做出决策（你只需修改以下部分）
        
        int bidValue = bidding();
        
        // 决策结束，输出结果（你只需修改以上部分）
        
        BotzoneIO::bid(bidValue);
    }
    else if (stage == Stage::PLAYING)
    {
        // 做出决策（你只需修改以下部分）
        
        // findFirstValid 函数可以用作修改的起点
        CardCombo myAction;// = lastValidCombo.findFirstValid(myCards.begin(), myCards.end());
        
        // 是合法牌
        assert(myAction.comboType != CardComboType::INVALID);
        
        assert(
               // 在上家没过牌的时候过牌
               (lastValidCombo.comboType != CardComboType::PASS && myAction.comboType == CardComboType::PASS) ||
               // 在上家没过牌的时候出打得过的牌
               (lastValidCombo.comboType != CardComboType::PASS && lastValidCombo.canBeBeatenBy(myAction)) ||
               // 在上家过牌的时候出合法牌
               (lastValidCombo.comboType == CardComboType::PASS && myAction.comboType != CardComboType::INVALID));
        
        // 决策结束，输出结果（你只需修改以上部分）
        
        BotzoneIO::play(myAction.cards.begin(), myAction.cards.end());
    }
}
