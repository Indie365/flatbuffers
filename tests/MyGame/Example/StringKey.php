<?php
// automatically generated by the FlatBuffers compiler, do not modify

namespace MyGame\Example;

use \Google\FlatBuffers\Struct;
use \Google\FlatBuffers\Table;
use \Google\FlatBuffers\ByteBuffer;
use \Google\FlatBuffers\FlatBufferBuilder;

class StringKey extends Table
{
    /**
     * @param ByteBuffer $bb
     * @return StringKey
     */
    public static function getRootAsStringKey(ByteBuffer $bb)
    {
        $obj = new StringKey();
        return ($obj->init($bb->getInt($bb->getPosition()) + $bb->getPosition(), $bb));
    }

    public static function StringKeyIdentifier()
    {
        return "MONS";
    }

    public static function StringKeyBufferHasIdentifier(ByteBuffer $buf)
    {
        return self::__has_identifier($buf, self::StringKeyIdentifier());
    }

    public static function StringKeyExtension()
    {
        return "mon";
    }

    /**
     * @param int $_i offset
     * @param ByteBuffer $_bb
     * @return StringKey
     **/
    public function init($_i, ByteBuffer $_bb)
    {
        $this->bb_pos = $_i;
        $this->bb = $_bb;
        return $this;
    }

    public function getK()
    {
        $o = $this->__offset(4);
        return $o != 0 ? $this->__string($o + $this->bb_pos) : null;
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return void
     */
    public static function startStringKey(FlatBufferBuilder $builder)
    {
        $builder->StartObject(1);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return StringKey
     */
    public static function createStringKey(FlatBufferBuilder $builder, $k)
    {
        $builder->startObject(1);
        self::addK($builder, $k);
        $o = $builder->endObject();
        $builder->required($o, 4);  // k
        return $o;
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param StringOffset
     * @return void
     */
    public static function addK(FlatBufferBuilder $builder, $k)
    {
        $builder->addOffsetX(0, $k, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return int table offset
     */
    public static function endStringKey(FlatBufferBuilder $builder)
    {
        $o = $builder->endObject();
        $builder->required($o, 4);  // k
        return $o;
    }
}
