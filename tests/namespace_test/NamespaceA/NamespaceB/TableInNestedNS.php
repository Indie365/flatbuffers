<?php
// automatically generated, do not modify

namespace NamespaceA\NamespaceB;

use \Google\FlatBuffers\Struct;
use \Google\FlatBuffers\Table;
use \Google\FlatBuffers\ByteBuffer;
use \Google\FlatBuffers\FlatBufferBuilder;

class TableInNestedNS extends Table
{
    /**
     * @param ByteBuffer $bb
     * @return TableInNestedNS
     */
    public static function getRootAsTableInNestedNS(ByteBuffer $bb)
    {
        $obj = new TableInNestedNS();
        return ($obj->init($bb->getInt($bb->getPosition()) + $bb->getPosition(), $bb));
    }

    /**
     * @param int $_i offset
     * @param ByteBuffer $_bb
     * @return TableInNestedNS
     **/
    public function init($_i, ByteBuffer $_bb)
    {
        $this->bb_pos = $_i;
        $this->bb = $_bb;
        return $this;
    }

    /**
     * @return int
     */
    public function getFoo()
    {
        $o = $this->__offset(4);
        return $o != 0 ? $this->bb->getInt($o + $this->bb_pos) : 0;
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return void
     */
    public static function startTableInNestedNS(FlatBufferBuilder $builder)
    {
        $builder->StartObject(1);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return TableInNestedNS
     */
    public static function createTableInNestedNS(FlatBufferBuilder $builder, $foo)
    {
        $builder->startObject(1);
        self::addFoo($builder, $foo);
        $o = $builder->endObject();
        return $o;
    }

    /**
     * @param FlatBufferBuilder $builder
     * @param int
     * @return void
     */
    public static function addFoo(FlatBufferBuilder $builder, $foo)
    {
        $builder->addIntX(0, $foo, 0);
    }

    /**
     * @param FlatBufferBuilder $builder
     * @return int table offset
     */
    public static function endTableInNestedNS(FlatBufferBuilder $builder)
    {
        $o = $builder->endObject();
        return $o;
    }
}
