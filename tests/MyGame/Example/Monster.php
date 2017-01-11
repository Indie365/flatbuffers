<?php
// automatically generated by the FlatBuffers compiler, do not modify

namespace MyGame\Example;

use \Google\FlatBuffers\Struct;
use \Google\FlatBuffers\Table;
use \Google\FlatBuffers\ByteBuffer;
use \Google\FlatBuffers\FlatBufferBuilder;

/// an example documentation comment: monster object
class Monster extends Table
{
    /**
     * @param ByteBuffer $bb
     * @return Monster
     */
    public static function getRootAsMonster(ByteBuffer $bb)
    {
        $obj = new Monster();
        return ($obj->init($bb->getInt($bb->getPosition()) + $bb->getPosition(), $bb));
    }

    public static function MonsterIdentifier()
    {
        return "MONS";
    }

    public static function MonsterBufferHasIdentifier(ByteBuffer $buf)
    {
        return self::__has_identifier($buf, self::MonsterIdentifier());
    }

    public static function MonsterExtension()
    {
        return "mon";
    }

    /**
     * @param int $_i offset
     * @param ByteBuffer $_bb
     * @return Monster
     **/
    public function init($_i, ByteBuffer $_bb)
    {
        $this->bb_pos = $_i;
        $this->bb = $_bb;
        return $this;
    }

    public function getPos()
    {
        $obj = new Vec3();
        $o = $this->__offset(4);
        return $o != 0 ? $obj->init($o + $this->bb_pos, $this->bb) : 0;
    }

    /**
     * @return short
     */
    public function getMana()
    {
        $o = $this->__offset(6);
        return $o != 0 ? $this->bb->getShort($o + $this->bb_pos) : 150;
    }

    /**
     * @return short
     */
    public function getHp()
    {
        $o = $this->__offset(8);
        return $o != 0 ? $this->bb->getShort($o + $this->bb_pos) : 100;
    }

    public function getName()
    {
        $o = $this->__offset(10);
        return $o != 0 ? $this->__string($o + $this->bb_pos) : null;
    }

    /**
     * @param int offset
     * @return byte
     */
    public function getInventory($j)
    {
        $o = $this->__offset(14);
        return $o != 0 ? $this->bb->getByte($this->__vector($o) + $j * 1) : 0;
    }

    /**
     * @return int
     */
    public function getInventoryLength()
    {
        $o = $this->__offset(14);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @return string
     */
    public function getInventoryBytes()
    {
        return $this->__vector_as_bytes(14);
    }

    /**
     * @return sbyte
     */
    public function getColor()
    {
        $o = $this->__offset(16);
        return $o != 0 ? $this->bb->getSbyte($o + $this->bb_pos) : \MyGame\Example\Color::Blue;
    }

    /**
     * @return byte
     */
    public function getTestType()
    {
        $o = $this->__offset(18);
        return $o != 0 ? $this->bb->getByte($o + $this->bb_pos) : \MyGame\Example\Any::NONE;
    }

    /**
     * @returnint
     */
    public function getTest($obj)
    {
        $o = $this->__offset(20);
        return $o != 0 ? $this->__union($obj, $o) : null;
    }

    /**
     * @returnVectorOffset
     */
    public function getTest4($j)
    {
        $o = $this->__offset(22);
        $obj = new Test();
        return $o != 0 ? $obj->init($this->__vector($o) + $j *4, $this->bb) : null;
    }

    /**
     * @return int
     */
    public function getTest4Length()
    {
        $o = $this->__offset(22);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return string
     */
    public function getTestarrayofstring($j)
    {
        $o = $this->__offset(24);
        return $o != 0 ? $this->__string($this->__vector($o) + $j * 4) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofstringLength()
    {
        $o = $this->__offset(24);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

/// an example documentation comment: this will end up in the generated code
/// multiline too
    /**
     * @returnVectorOffset
     */
    public function getTestarrayoftables($j)
    {
        $o = $this->__offset(26);
        $obj = new Monster();
        return $o != 0 ? $obj->init($this->__indirect($this->__vector($o) + $j * 4), $this->bb) : null;
    }

    /**
     * @return int
     */
    public function getTestarrayoftablesLength()
    {
        $o = $this->__offset(26);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    public function getEnemy()
    {
        $obj = new Monster();
        $o = $this->__offset(28);
        return $o != 0 ? $obj->init($this->__indirect($o + $this->bb_pos), $this->bb) : 0;
    }

    /**
     * @param int offset
     * @return byte
     */
    public function getTestnestedflatbuffer($j)
    {
        $o = $this->__offset(30);
        return $o != 0 ? $this->bb->getByte($this->__vector($o) + $j * 1) : 0;
    }

    /**
     * @return int
     */
    public function getTestnestedflatbufferLength()
    {
        $o = $this->__offset(30);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @return string
     */
    public function getTestnestedflatbufferBytes()
    {
        return $this->__vector_as_bytes(30);
    }

    public function getTestempty()
    {
        $obj = new Stat();
        $o = $this->__offset(32);
        return $o != 0 ? $obj->init($this->__indirect($o + $this->bb_pos), $this->bb) : 0;
    }

    /**
     * @return bool
     */
    public function getTestbool()
    {
        $o = $this->__offset(34);
        return $o != 0 ? $this->bb->getBool($o + $this->bb_pos) : false;
    }

    /**
     * @return int
     */
    public function getTesthashs32Fnv1()
    {
        $o = $this->__offset(36);
        return $o != 0 ? $this->bb->getInt($o + $this->bb_pos) : 0;
    }

    /**
     * @return uint
     */
    public function getTesthashu32Fnv1()
    {
        $o = $this->__offset(38);
        return $o != 0 ? $this->bb->getUint($o + $this->bb_pos) : 0;
    }

    /**
     * @return long
     */
    public function getTesthashs64Fnv1()
    {
        $o = $this->__offset(40);
        return $o != 0 ? $this->bb->getLong($o + $this->bb_pos) : 0;
    }

    /**
     * @return ulong
     */
    public function getTesthashu64Fnv1()
    {
        $o = $this->__offset(42);
        return $o != 0 ? $this->bb->getUlong($o + $this->bb_pos) : 0;
    }

    /**
     * @return int
     */
    public function getTesthashs32Fnv1a()
    {
        $o = $this->__offset(44);
        return $o != 0 ? $this->bb->getInt($o + $this->bb_pos) : 0;
    }

    /**
     * @return uint
     */
    public function getTesthashu32Fnv1a()
    {
        $o = $this->__offset(46);
        return $o != 0 ? $this->bb->getUint($o + $this->bb_pos) : 0;
    }

    /**
     * @return long
     */
    public function getTesthashs64Fnv1a()
    {
        $o = $this->__offset(48);
        return $o != 0 ? $this->bb->getLong($o + $this->bb_pos) : 0;
    }

    /**
     * @return ulong
     */
    public function getTesthashu64Fnv1a()
    {
        $o = $this->__offset(50);
        return $o != 0 ? $this->bb->getUlong($o + $this->bb_pos) : 0;
    }

    /**
     * @param int offset
     * @return bool
     */
    public function getTestarrayofbools($j)
    {
        $o = $this->__offset(52);
        return $o != 0 ? $this->bb->getBool($this->__vector($o) + $j * 1) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofboolsLength()
    {
        $o = $this->__offset(52);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @return float
     */
    public function getTestf()
    {
        $o = $this->__offset(54);
        return $o != 0 ? $this->bb->getFloat($o + $this->bb_pos) : 3.14159;
    }

    /**
     * @return float
     */
    public function getTestf2()
    {
        $o = $this->__offset(56);
        return $o != 0 ? $this->bb->getFloat($o + $this->bb_pos) : 3.0;
    }

    /**
     * @return float
     */
    public function getTestf3()
    {
        $o = $this->__offset(58);
        return $o != 0 ? $this->bb->getFloat($o + $this->bb_pos) : 0.0;
    }

    /**
     * @param int offset
     * @return string
     */
    public function getTestarrayofstring2($j)
    {
        $o = $this->__offset(60);
        return $o != 0 ? $this->__string($this->__vector($o) + $j * 4) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofstring2Length()
    {
        $o = $this->__offset(60);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return sbyte
     */
    public function getTestarrayofbytes($j)
    {
        $o = $this->__offset(62);
        return $o != 0 ? $this->bb->getSbyte($this->__vector($o) + $j * 1) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofbytesLength()
    {
        $o = $this->__offset(62);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return short
     */
    public function getTestarrayofshort($j)
    {
        $o = $this->__offset(64);
        return $o != 0 ? $this->bb->getShort($this->__vector($o) + $j * 2) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofshortLength()
    {
        $o = $this->__offset(64);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return ushort
     */
    public function getTestarrayofushort($j)
    {
        $o = $this->__offset(66);
        return $o != 0 ? $this->bb->getUshort($this->__vector($o) + $j * 2) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofushortLength()
    {
        $o = $this->__offset(66);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return int
     */
    public function getTestarrayofint($j)
    {
        $o = $this->__offset(68);
        return $o != 0 ? $this->bb->getInt($this->__vector($o) + $j * 4) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofintLength()
    {
        $o = $this->__offset(68);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return uint
     */
    public function getTestarrayofuint($j)
    {
        $o = $this->__offset(70);
        return $o != 0 ? $this->bb->getUint($this->__vector($o) + $j * 4) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofuintLength()
    {
        $o = $this->__offset(70);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return long
     */
    public function getTestarrayoflong($j)
    {
        $o = $this->__offset(72);
        return $o != 0 ? $this->bb->getLong($this->__vector($o) + $j * 8) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayoflongLength()
    {
        $o = $this->__offset(72);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return ulong
     */
    public function getTestarrayofulong($j)
    {
        $o = $this->__offset(74);
        return $o != 0 ? $this->bb->getUlong($this->__vector($o) + $j * 8) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofulongLength()
    {
        $o = $this->__offset(74);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return float
     */
    public function getTestarrayoffloat($j)
    {
        $o = $this->__offset(76);
        return $o != 0 ? $this->bb->getFloat($this->__vector($o) + $j * 4) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayoffloatLength()
    {
        $o = $this->__offset(76);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @param int offset
     * @return double
     */
    public function getTestarrayofdouble($j)
    {
        $o = $this->__offset(78);
        return $o != 0 ? $this->bb->getDouble($this->__vector($o) + $j * 8) : 0;
    }

    /**
     * @return int
     */
    public function getTestarrayofdoubleLength()
    {
        $o = $this->__offset(78);
        return $o != 0 ? $this->__vector_len($o) : 0;
    }

    /**
     * @return double
     */
    public function getTestdouble()
    {
        $o = $this->__offset(80);
        return $o != 0 ? $this->bb->getDouble($o + $this->bb_pos) : 0.0;
    }

    /**
     * @return sbyte
     */
    public function getTestbyte()
    {
        $o = $this->__offset(82);
        return $o != 0 ? $this->bb->getSbyte($o + $this->bb_pos) : 0;
    }

    /**
     * @return byte
     */
    public function getTestubyte()
    {
        $o = $this->__offset(84);
        return $o != 0 ? $this->bb->getByte($o + $this->bb_pos) : 0;
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return void
     */
    public static function startMonster(FlatBufferBuilder $builder)
    {
        $builder->StartObject(41);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return Monster
     */
    public static function createMonster(FlatBufferBuilder $builder, $pos, $mana, $hp, $name, $inventory, $color, $test_type, $test, $test4, $testarrayofstring, $testarrayoftables, $enemy, $testnestedflatbuffer, $testempty, $testbool, $testhashs32_fnv1, $testhashu32_fnv1, $testhashs64_fnv1, $testhashu64_fnv1, $testhashs32_fnv1a, $testhashu32_fnv1a, $testhashs64_fnv1a, $testhashu64_fnv1a, $testarrayofbools, $testf, $testf2, $testf3, $testarrayofstring2, $testarrayofbytes, $testarrayofshort, $testarrayofushort, $testarrayofint, $testarrayofuint, $testarrayoflong, $testarrayofulong, $testarrayoffloat, $testarrayofdouble, $testdouble, $testbyte, $testubyte)
    {
        $builder->startObject(41);
        self::addPos($builder, $pos);
        self::addMana($builder, $mana);
        self::addHp($builder, $hp);
        self::addName($builder, $name);
        self::addInventory($builder, $inventory);
        self::addColor($builder, $color);
        self::addTestType($builder, $test_type);
        self::addTest($builder, $test);
        self::addTest4($builder, $test4);
        self::addTestarrayofstring($builder, $testarrayofstring);
        self::addTestarrayoftables($builder, $testarrayoftables);
        self::addEnemy($builder, $enemy);
        self::addTestnestedflatbuffer($builder, $testnestedflatbuffer);
        self::addTestempty($builder, $testempty);
        self::addTestbool($builder, $testbool);
        self::addTesthashs32Fnv1($builder, $testhashs32_fnv1);
        self::addTesthashu32Fnv1($builder, $testhashu32_fnv1);
        self::addTesthashs64Fnv1($builder, $testhashs64_fnv1);
        self::addTesthashu64Fnv1($builder, $testhashu64_fnv1);
        self::addTesthashs32Fnv1a($builder, $testhashs32_fnv1a);
        self::addTesthashu32Fnv1a($builder, $testhashu32_fnv1a);
        self::addTesthashs64Fnv1a($builder, $testhashs64_fnv1a);
        self::addTesthashu64Fnv1a($builder, $testhashu64_fnv1a);
        self::addTestarrayofbools($builder, $testarrayofbools);
        self::addTestf($builder, $testf);
        self::addTestf2($builder, $testf2);
        self::addTestf3($builder, $testf3);
        self::addTestarrayofstring2($builder, $testarrayofstring2);
        self::addTestarrayofbytes($builder, $testarrayofbytes);
        self::addTestarrayofshort($builder, $testarrayofshort);
        self::addTestarrayofushort($builder, $testarrayofushort);
        self::addTestarrayofint($builder, $testarrayofint);
        self::addTestarrayofuint($builder, $testarrayofuint);
        self::addTestarrayoflong($builder, $testarrayoflong);
        self::addTestarrayofulong($builder, $testarrayofulong);
        self::addTestarrayoffloat($builder, $testarrayoffloat);
        self::addTestarrayofdouble($builder, $testarrayofdouble);
        self::addTestdouble($builder, $testdouble);
        self::addTestbyte($builder, $testbyte);
        self::addTestubyte($builder, $testubyte);
        $o = $builder->endObject();
        $builder->required($o, 10);  // name
        return $o;
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int
     * @return void
     */
    public static function addPos(FlatBufferBuilder $builder, $pos)
    {
        $builder->addStructX(0, $pos, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param short
     * @return void
     */
    public static function addMana(FlatBufferBuilder $builder, $mana)
    {
        $builder->addShortX(1, $mana, 150);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param short
     * @return void
     */
    public static function addHp(FlatBufferBuilder $builder, $hp)
    {
        $builder->addShortX(2, $hp, 100);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param StringOffset
     * @return void
     */
    public static function addName(FlatBufferBuilder $builder, $name)
    {
        $builder->addOffsetX(3, $name, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addInventory(FlatBufferBuilder $builder, $inventory)
    {
        $builder->addOffsetX(5, $inventory, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createInventoryVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(1, count($data), 1);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addByte($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startInventoryVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(1, $numElems, 1);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param sbyte
     * @return void
     */
    public static function addColor(FlatBufferBuilder $builder, $color)
    {
        $builder->addSbyteX(6, $color, 8);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param byte
     * @return void
     */
    public static function addTestType(FlatBufferBuilder $builder, $testType)
    {
        $builder->addByteX(7, $testType, 0);
    }

    public static function addTest(FlatBufferBuilder $builder, $offset)
    {
        $builder->addOffsetX(8, $offset, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTest4(FlatBufferBuilder $builder, $test4)
    {
        $builder->addOffsetX(9, $test4, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTest4Vector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(4, count($data), 2);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addOffset($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTest4Vector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(4, $numElems, 2);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofstring(FlatBufferBuilder $builder, $testarrayofstring)
    {
        $builder->addOffsetX(10, $testarrayofstring, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofstringVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(4, count($data), 4);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addOffset($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofstringVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(4, $numElems, 4);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayoftables(FlatBufferBuilder $builder, $testarrayoftables)
    {
        $builder->addOffsetX(11, $testarrayoftables, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayoftablesVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(4, count($data), 4);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addOffset($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayoftablesVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(4, $numElems, 4);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int
     * @return void
     */
    public static function addEnemy(FlatBufferBuilder $builder, $enemy)
    {
        $builder->addOffsetX(12, $enemy, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestnestedflatbuffer(FlatBufferBuilder $builder, $testnestedflatbuffer)
    {
        $builder->addOffsetX(13, $testnestedflatbuffer, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestnestedflatbufferVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(1, count($data), 1);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addByte($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestnestedflatbufferVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(1, $numElems, 1);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int
     * @return void
     */
    public static function addTestempty(FlatBufferBuilder $builder, $testempty)
    {
        $builder->addOffsetX(14, $testempty, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param bool
     * @return void
     */
    public static function addTestbool(FlatBufferBuilder $builder, $testbool)
    {
        $builder->addBoolX(15, $testbool, false);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int
     * @return void
     */
    public static function addTesthashs32Fnv1(FlatBufferBuilder $builder, $testhashs32Fnv1)
    {
        $builder->addIntX(16, $testhashs32Fnv1, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param uint
     * @return void
     */
    public static function addTesthashu32Fnv1(FlatBufferBuilder $builder, $testhashu32Fnv1)
    {
        $builder->addUintX(17, $testhashu32Fnv1, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param long
     * @return void
     */
    public static function addTesthashs64Fnv1(FlatBufferBuilder $builder, $testhashs64Fnv1)
    {
        $builder->addLongX(18, $testhashs64Fnv1, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param ulong
     * @return void
     */
    public static function addTesthashu64Fnv1(FlatBufferBuilder $builder, $testhashu64Fnv1)
    {
        $builder->addUlongX(19, $testhashu64Fnv1, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int
     * @return void
     */
    public static function addTesthashs32Fnv1a(FlatBufferBuilder $builder, $testhashs32Fnv1a)
    {
        $builder->addIntX(20, $testhashs32Fnv1a, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param uint
     * @return void
     */
    public static function addTesthashu32Fnv1a(FlatBufferBuilder $builder, $testhashu32Fnv1a)
    {
        $builder->addUintX(21, $testhashu32Fnv1a, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param long
     * @return void
     */
    public static function addTesthashs64Fnv1a(FlatBufferBuilder $builder, $testhashs64Fnv1a)
    {
        $builder->addLongX(22, $testhashs64Fnv1a, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param ulong
     * @return void
     */
    public static function addTesthashu64Fnv1a(FlatBufferBuilder $builder, $testhashu64Fnv1a)
    {
        $builder->addUlongX(23, $testhashu64Fnv1a, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofbools(FlatBufferBuilder $builder, $testarrayofbools)
    {
        $builder->addOffsetX(24, $testarrayofbools, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofboolsVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(1, count($data), 1);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addBool($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofboolsVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(1, $numElems, 1);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param float
     * @return void
     */
    public static function addTestf(FlatBufferBuilder $builder, $testf)
    {
        $builder->addFloatX(25, $testf, 3.14159);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param float
     * @return void
     */
    public static function addTestf2(FlatBufferBuilder $builder, $testf2)
    {
        $builder->addFloatX(26, $testf2, 3.0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param float
     * @return void
     */
    public static function addTestf3(FlatBufferBuilder $builder, $testf3)
    {
        $builder->addFloatX(27, $testf3, 0.0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofstring2(FlatBufferBuilder $builder, $testarrayofstring2)
    {
        $builder->addOffsetX(28, $testarrayofstring2, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofstring2Vector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(4, count($data), 4);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addOffset($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofstring2Vector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(4, $numElems, 4);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofbytes(FlatBufferBuilder $builder, $testarrayofbytes)
    {
        $builder->addOffsetX(29, $testarrayofbytes, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofbytesVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(1, count($data), 1);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addSbyte($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofbytesVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(1, $numElems, 1);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofshort(FlatBufferBuilder $builder, $testarrayofshort)
    {
        $builder->addOffsetX(30, $testarrayofshort, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofshortVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(2, count($data), 2);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addShort($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofshortVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(2, $numElems, 2);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofushort(FlatBufferBuilder $builder, $testarrayofushort)
    {
        $builder->addOffsetX(31, $testarrayofushort, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofushortVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(2, count($data), 2);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addUshort($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofushortVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(2, $numElems, 2);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofint(FlatBufferBuilder $builder, $testarrayofint)
    {
        $builder->addOffsetX(32, $testarrayofint, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofintVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(4, count($data), 4);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addInt($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofintVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(4, $numElems, 4);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofuint(FlatBufferBuilder $builder, $testarrayofuint)
    {
        $builder->addOffsetX(33, $testarrayofuint, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofuintVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(4, count($data), 4);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addUint($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofuintVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(4, $numElems, 4);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayoflong(FlatBufferBuilder $builder, $testarrayoflong)
    {
        $builder->addOffsetX(34, $testarrayoflong, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayoflongVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(8, count($data), 8);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addLong($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayoflongVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(8, $numElems, 8);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofulong(FlatBufferBuilder $builder, $testarrayofulong)
    {
        $builder->addOffsetX(35, $testarrayofulong, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofulongVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(8, count($data), 8);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addUlong($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofulongVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(8, $numElems, 8);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayoffloat(FlatBufferBuilder $builder, $testarrayoffloat)
    {
        $builder->addOffsetX(36, $testarrayoffloat, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayoffloatVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(4, count($data), 4);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addFloat($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayoffloatVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(4, $numElems, 4);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param VectorOffset
     * @return void
     */
    public static function addTestarrayofdouble(FlatBufferBuilder $builder, $testarrayofdouble)
    {
        $builder->addOffsetX(37, $testarrayofdouble, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param array offset array
     * @return int vector offset
     */
    public static function createTestarrayofdoubleVector(FlatBufferBuilder $builder, array $data)
    {
        $builder->startVector(8, count($data), 8);
        for ($i = count($data) - 1; $i >= 0; $i--) {
            $builder->addDouble($data[$i]);
        }
        return $builder->endVector();
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int $numElems
     * @return void
     */
    public static function startTestarrayofdoubleVector(FlatBufferBuilder $builder, $numElems)
    {
        $builder->startVector(8, $numElems, 8);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param double
     * @return void
     */
    public static function addTestdouble(FlatBufferBuilder $builder, $testdouble)
    {
        $builder->addDoubleX(38, $testdouble, 0.0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param sbyte
     * @return void
     */
    public static function addTestbyte(FlatBufferBuilder $builder, $testbyte)
    {
        $builder->addSbyteX(39, $testbyte, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param byte
     * @return void
     */
    public static function addTestubyte(FlatBufferBuilder $builder, $testubyte)
    {
        $builder->addByteX(40, $testubyte, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return int table offset
     */
    public static function endMonster(FlatBufferBuilder $builder)
    {
        $o = $builder->endObject();
        $builder->required($o, 10);  // name
        return $o;
    }

    public static function finishMonsterBuffer(FlatBufferBuilder $builder, $offset)
    {
        $builder->finish($offset, "MONS");
    }
}
