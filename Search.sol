pragma solidity >=0.4.22 <=0.6.0;
pragma experimental ABIEncoderV2;

contract Search{
    
    // w1IdNumber
    // uint constant c = 2;

    // CEDB dictionary
    mapping(bytes32 => bytes []) public CEDB;
    mapping(bytes32 => bytes32) public CEDB_tc;
    mapping(bytes32 => uint) public CEDB_delta;
    mapping(bytes32 => bytes32) public CEDB_y;

    bytes public pp;

    // CBSIndex Set
    struct Set{
        bytes [] values;
        mapping(bytes => bool) is_in;
    }

    Set my_CBSIndex;

    // CPT dictionary
    mapping(bytes32 => bytes32) public CPT_stc;
    mapping(bytes32 => uint) public CPT_c;

    // ST_w
    mapping(uint => bytes []) public ST_w;

    // stag_w
    // bytes32 public stag_w;

    // st_i
    // bytes16 [] public st = new bytes16 [] (c);
    mapping(uint => bytes32) public st;

    // Result set R, D
    // mapping(bytes32 => bytes []) public R;
    // mapping(bytes32 => bytes []) public D;
    bytes32 [] public returnR_u;
    bytes32 [] public returnD_u;
    bytes [] public R_cipher;
    bytes [][] public cipher_onebyone;

    // uint [] public y_flag_all;

    function get_st(uint c)public view returns(bytes32){
        return st[c];
    }

    // CEDB storage
    function set_CEDB(bytes32 _u, bytes _C_0, bytes _C_1, bytes _C_2) public{
        CEDB[_u].push(_C_0);
        CEDB[_u].push(_C_1);
        CEDB[_u].push(_C_2);
    }

    function set_CEDB_tc(bytes32 u, bytes32 t_c) public{
        CEDB_tc[u] = t_c;
    }

    function set_CEDB_tc_batch(bytes32 [] memory u, bytes32 [] memory t_c, uint len) public{
        for(uint j = 0; j < len; j++){
            CEDB_tc[u[j]] = t_c[j];
        }
    }

    function set_CEDB_delta(bytes32 [] memory u, uint [] memory delta, uint len) public{
        for(uint i = 0; i < len; i++){
            CEDB_delta[u[i]] = delta[i];
        }
    }

    function set_CEDB_y(bytes32 [] memory u, bytes32 [] memory y, uint len)public{
        for(uint i = 0; i < len; i++){
            CEDB_y[u[i]] = y[i];
        }
    }

    function set_CEDB_batch(bytes32 [] memory _u, bytes [] memory _C_0, bytes [] memory _C_1, bytes [] memory _C_2, bytes [] memory _y, uint _len) public{
        for(uint i = 0; i < _len; i++){
            CEDB[_u[i]] = [_C_0[i], _C_1[i], _C_2[i], _y[i]];
        }
    }

    // CEDB find
    function get_CEDB_value(bytes32 _u, uint _index) public view returns (bytes){
        return CEDB[_u][_index];
    }

    function get_CEDB_tc(bytes32 u) public view returns(bytes32){
        return CEDB_tc[u];
    }

    function get_CEDB_delta(bytes32 u) public view returns(uint){
        return CEDB_delta[u];
    }

    function get_CEDB_y(bytes32 u) public view returns(bytes32){
        return CEDB_y[u];
    }

    // CBSIndex add
    function CBSIndex_add(bytes [] memory xtags, uint _len) public{
        for(uint i = 0; i < _len; i++){
            // bytes a = xtags[i];
            if(!my_CBSIndex.is_in[xtags[i]]){
            my_CBSIndex.values.push(xtags[i]);
            my_CBSIndex.is_in[xtags[i]] = true;
            }
        }
    }


    // CBSIndex existence
    function CBSIndex_exist(bytes b) public view returns(bool){
        return my_CBSIndex.is_in[b];
    }

    // CPT storage
    function set_CPT_stc(bytes32 [] memory l, bytes32 [] memory stc, uint _len) public{
        for(uint i = 0; i < _len; i++){
           CPT_stc[l[i]] = stc[i];
        }
    }

    function set_CPT_c(bytes32 [] memory l, uint [] memory c, uint len) public{
        for(uint i = 0; i < len; i++){
           CPT_c[l[i]] = c[i];
        }
    }

    function get_CPT_stc(bytes32 _l) public view returns(bytes32){
        return CPT_stc[_l];
    }

    function get_CPT_c(bytes32 _l) public view returns(uint){
        return CPT_c[_l];
    }

    // ST_w storage
    function set_ST_w(uint _c, bytes [] memory _searchtoken, uint _per_token_number) public{
        for(uint j = 0; j < _per_token_number; j++){
            // bytes m = _searchtoken[j];
            ST_w[_c].push(_searchtoken[j]);
        }
    }

    function get_ST_w(uint _c, uint _index) public view returns(bytes){
        return ST_w[_c][_index];
    }

    // bytes concatenation
    function concate(bytes16 _a, bytes32 _b) public view returns (bytes memory){
        return abi.encodePacked(_a, _b);
    }

    //int to bytes
    // function toBytes(uint _x) public view returns (bytes32 _b) {
    //     return bytes32(_x);
    // }

    function setP(bytes p) public{
        pp = p;
    }

    function getP() public view returns(bytes){
        return pp;
    }

    // exponent
    function expmod(bytes g, uint256 x, bytes p) public view returns (bytes) {
      require(p.length == 384,"unqualified length of p");
      require(g.length == 384,"unqualified length of g");
      bytes memory input = abi.encodePacked(bytes32(g.length),bytes32(0x20),bytes32(p.length),g,bytes32(x),p);
      bytes memory result = new bytes(384);
      bytes memory pointer = new bytes(384);
      assembly {
          if iszero(staticcall(sub(gas, 2000), 0x05, add(input,0x20), 0x380, add(pointer,0x20), 0x180 )) {
             revert(0, 0)
          }
      }
      for(uint i =0; i<12;i++) {
          bytes32 value;
          uint256 start = 32*i;
          assembly {
              value := mload(add(add(pointer,0x20),start))
          }
        //   return value;
          for(uint j=0;j<32;j++) {
              result[start+j] = value[j];
          }
      }
      return result;
    }

    // search
    function onchain_search(bytes16 stag_w, bytes32 st_c, uint c, uint per_token_number) public{
        st[c] = st_c;
        for(uint i = c; i > 0; i--){
            bytes memory concatenation = concate(stag_w, st[i]);
            bytes32 u = keccak256(abi.encodePacked(concatenation));
            bytes32 test_y = CEDB_y[u];
            uint delta = CEDB_delta[u];
            bytes32 t_i = CEDB_tc[u];

            if(delta == 1){
                // D[u] = [get_CEDB_value(u, 0), get_CEDB_value(u, 1), get_CEDB_value(u, 2)];
                returnD_u.push(u);
            }
            // returnR_u.push(u);

            // bytes[] test_tag;
            // test all exist
            uint y_flag = 0;
            for(uint j = 0; j < per_token_number; j++){
                bytes memory token_c_j = ST_w[i][j];
                bytes memory test_token_y = expmod(token_c_j, uint(test_y), pp);
                // test_tag.push(test_token_y);
                if(CBSIndex_exist(test_token_y)){
                    y_flag = y_flag+1;
                }
            }
            // y_flag_all.push(y_flag);
            if(y_flag == per_token_number){
                returnR_u.push(u);
            }
            // AES decrypt
            // st[i-1] = x_o_r(t_i, st[i]);
            st[i-1] = t_i ^ st[i];
        }
    }

    function get_returnD_u() public view returns(bytes32 []){
        return returnD_u;
    }

    function get_returnR_u() public view returns(bytes32 []){
        return returnR_u;
    }

    function set_R_cipher(bytes32 R_u) public{
        R_cipher = CEDB[R_u];
    }

    function get_R_cipher() public view returns(bytes[]){
        return R_cipher;
    }

    function set_cipher_onebyone(bytes32 R_u) public {
        cipher_onebyone.push(CEDB[R_u]);
    }

    function get_cipher_onebyone() public view returns(bytes [][]){
        return cipher_onebyone;
    }

    // function get_y_flag_all() public view returns(uint []){
    //     return y_flag_all;
    // }
}

